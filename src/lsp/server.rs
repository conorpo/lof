use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    io::{self, BufRead, Write},
    path::PathBuf,
};

use super::{protocol, text};
use crate::{modules::ModuleLoader, parse};

struct Document {
    path: PathBuf,
    source: String,
    version: i64,
}

#[derive(Default)]
struct Session {
    documents: BTreeMap<String, Document>,
}

impl Session {
    fn loader(&self) -> ModuleLoader {
        let mut loader = ModuleLoader::new();
        for document in self.documents.values() {
            // File URIs already provide absolute paths, so current-directory
            // lookup cannot fail here. Overlays also support unsaved new files.
            loader
                .set_source(&document.path, document.source.clone())
                .expect("absolute file URI");
        }
        loader
    }

    fn validate(&self, output: &mut impl Write) -> io::Result<()> {
        let mut loader = self.loader();
        for (uri, document) in &self.documents {
            let diagnostics = match loader.load(&document.path) {
                Ok(_) => vec![],
                Err(error) => {
                    let start = error.offset().min(document.source.len());
                    let end = document
                        .source
                        .get(start..)
                        .and_then(|s| s.chars().next())
                        .map(|ch| start + ch.len_utf8())
                        .unwrap_or(start);
                    vec![json!({"range": text::range(&document.source, start, end),
                        "severity": 1, "source": "lof", "message": error.to_string()})]
                }
            };
            protocol::write(
                output,
                &json!({"jsonrpc":"2.0", "method":"textDocument/publishDiagnostics",
                "params":{"uri":uri, "version":document.version, "diagnostics":diagnostics}}),
            )?;
        }
        Ok(())
    }

    fn complete(&self, uri: &str, position: &Value) -> Vec<Value> {
        let Some(document) = self.documents.get(uri) else {
            return vec![];
        };
        let at = text::offset(&document.source, position);
        let before = &document.source[..at];
        let start = before
            .char_indices()
            .rev()
            .find(|(_, ch)| !ch.is_alphanumeric() && !matches!(ch, '_' | '\'' | ':'))
            .map(|(index, ch)| index + ch.len_utf8())
            .unwrap_or(0);
        let prefix = &before[start..];
        let mut loader = self.loader();
        let mut candidates: BTreeMap<String, String> = BTreeMap::new();
        if let Ok(module) = loader.load(&document.path) {
            for (name, id) in module.scope() {
                let ty = loader
                    .environment()
                    .definition(id)
                    .expect("checked declaration")
                    .ty();
                candidates.insert(name.clone(), format!("{ty:?}"));
            }
        } else if let Ok(syntax) = parse::parse_module(&document.source) {
            // Offer declared names while an unfinished body is being repaired.
            for definition in syntax.definitions {
                candidates.insert(definition.name, "LOF definition".to_owned());
            }
            for import in syntax.imports {
                if let Some(parent) = document.path.parent() {
                    if let Ok(module) = loader.load(parent.join(import.path)) {
                        for name in module.exports().keys() {
                            candidates.insert(
                                format!("{}::{name}", import.alias),
                                "imported LOF definition".to_owned(),
                            );
                        }
                    }
                }
            }
        }
        // Incomplete declarations must not prevent completion after `Alias::`.
        // Parse just the leading import declarations if the whole file fails.
        for line in document.source.lines() {
            if line.trim_start().starts_with("import ") {
                if let Ok(syntax) = parse::parse_module(line) {
                    for import in syntax.imports {
                        if let Some(parent) = document.path.parent() {
                            if let Ok(module) = loader.load(parent.join(import.path)) {
                                for name in module.exports().keys() {
                                    candidates
                                        .entry(format!("{}::{name}", import.alias))
                                        .or_insert("imported LOF definition".to_owned());
                                }
                            }
                        }
                    }
                }
            }
        }
        if !prefix.contains("::") {
            for keyword in [
                "let",
                "export",
                "import",
                "Nat",
                "Empty",
                "Unit",
                "tt",
                "ind0",
                "ind1",
                "rec0",
                "rec1",
                "U0",
                "U1",
                "λ",
                "Π",
                "Σ",
                "refl",
                "Succ",
                "ind_nat",
                "ind_id",
                "ind_Σ",
                "ind_coproduct",
                "recNat",
                "recId",
                "rec_Σ",
                "recCoproduct",
            ] {
                candidates
                    .entry(keyword.to_owned())
                    .or_insert("LOF syntax".to_owned());
            }
        }
        let qualifier = prefix
            .rsplit_once("::")
            .map(|(alias, _)| format!("{alias}::"));
        candidates.into_iter().filter(|(name, _)| name.starts_with(prefix)).map(|(name, detail)| {
            let (label, replace_start) = if let Some(qualifier) = &qualifier {
                (name.strip_prefix(qualifier).unwrap_or(&name), start + qualifier.len())
            } else { (name.as_str(), start) };
            json!({"label":label, "kind":6, "detail":detail,
                "textEdit":{"range":text::range(&document.source, replace_start, at), "newText":label}})
        }).collect()
    }
}

/// Serve UTF-16 LSP over Content-Length framed JSON-RPC on stdio.
/// Diagnostics use the same checked module loader as the CLI and Rust tests.
pub fn run(mut input: impl BufRead, mut output: impl Write) -> io::Result<i32> {
    let mut session = Session::default();
    let mut initialized = false;
    let mut shutdown = false;
    while let Some(message) = protocol::read(&mut input)? {
        let method = message["method"].as_str().unwrap_or("");
        let id = message.get("id").cloned();
        let params = &message["params"];
        if method == "exit" {
            return Ok(if shutdown { 0 } else { 1 });
        }
        let result = match method {
            "initialize" if !initialized => {
                initialized = true;
                Some(Ok(json!({"capabilities":{
                    "positionEncoding":"utf-16",
                    "textDocumentSync":{"openClose":true,"change":1,"save":{"includeText":true}},
                    "completionProvider":{"triggerCharacters":[":"]}
                },"serverInfo":{"name":"lof-lsp","version":env!("CARGO_PKG_VERSION")}})))
            }
            _ if !initialized || shutdown => {
                Some(Err((-32002, "server is not initialized or has shut down")))
            }
            "shutdown" => {
                shutdown = true;
                Some(Ok(Value::Null))
            }
            "initialized" | "$/cancelRequest" | "$/setTrace" => None,
            "textDocument/didOpen" => {
                let item = &params["textDocument"];
                if let Some(uri) = item["uri"].as_str() {
                    if let Some(path) = text::file_path(uri) {
                        session.documents.insert(
                            uri.to_owned(),
                            Document {
                                path,
                                source: item["text"].as_str().unwrap_or("").to_owned(),
                                version: item["version"].as_i64().unwrap_or(0),
                            },
                        );
                        session.validate(&mut output)?;
                    }
                }
                None
            }
            "textDocument/didChange" => {
                if let Some(uri) = params["textDocument"]["uri"].as_str() {
                    if let Some(document) = session.documents.get_mut(uri) {
                        if let Some(change) = params["contentChanges"]
                            .as_array()
                            .and_then(|changes| changes.last())
                        {
                            document.source = change["text"].as_str().unwrap_or("").to_owned();
                            document.version = params["textDocument"]["version"]
                                .as_i64()
                                .unwrap_or(document.version);
                        }
                    }
                    session.validate(&mut output)?;
                }
                None
            }
            "textDocument/didClose" => {
                if let Some(uri) = params["textDocument"]["uri"].as_str() {
                    session.documents.remove(uri);
                    protocol::write(
                        &mut output,
                        &json!({"jsonrpc":"2.0", "method":"textDocument/publishDiagnostics",
                        "params":{"uri":uri,"diagnostics":[]}}),
                    )?;
                    session.validate(&mut output)?;
                }
                None
            }
            "textDocument/didSave" | "workspace/didChangeWatchedFiles" => {
                session.validate(&mut output)?;
                None
            }
            "textDocument/completion" => Some(Ok(json!(session.complete(
                params["textDocument"]["uri"].as_str().unwrap_or(""),
                &params["position"]
            )))),
            _ => Some(Err((-32601, "method not supported"))),
        };
        if let (Some(id), Some(result)) = (id, result) {
            let response = match result {
                Ok(result) => json!({"jsonrpc":"2.0", "id":id, "result":result}),
                Err((code, message)) => {
                    json!({"jsonrpc":"2.0", "id":id, "error":{"code":code,"message":message}})
                }
            };
            protocol::write(&mut output, &response)?;
        }
    }
    Ok(0)
}
