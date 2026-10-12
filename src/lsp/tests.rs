use super::{protocol, run, text};
use serde_json::{Value, json};
use std::io::Cursor;

fn conversation(messages: Vec<Value>) -> Vec<Value> {
    let mut input = Vec::new();
    for message in messages {
        protocol::write(&mut input, &message).unwrap();
    }
    let mut output = Vec::new();
    assert_eq!(run(Cursor::new(input), &mut output).unwrap(), 0);
    let mut output = Cursor::new(output);
    let mut messages = Vec::new();
    while let Some(message) = protocol::read(&mut output).unwrap() {
        messages.push(message);
    }
    messages
}

fn initialize() -> Value {
    json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{}})
}
fn open(uri: &str, source: &str) -> Value {
    json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
        "uri":uri,"languageId":"lof","version":1,"text":source}}})
}
fn change(uri: &str, source: &str) -> Value {
    json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
        "textDocument":{"uri":uri,"version":2},"contentChanges":[{"text":source}]}})
}

#[test]
fn diagnostics_report_type_errors_and_clear_after_an_unsaved_edit() {
    let uri = "file:///tmp/lof-lsp-unit/new.lof";
    let responses = conversation(vec![
        initialize(),
        open(uri, "export let bad=Succ(Nat);"),
        change(uri, "export let id=λ(x:Nat).x;"),
        json!({"id":2,"method":"shutdown"}),
        json!({"method":"exit"}),
    ]);
    assert_eq!(
        responses[0]["result"]["capabilities"]["positionEncoding"],
        "utf-16"
    );
    let diagnostics: Vec<_> = responses
        .iter()
        .filter(|r| r["method"] == "textDocument/publishDiagnostics")
        .collect();
    assert_eq!(
        diagnostics[0]["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(
        diagnostics[0]["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("type mismatch")
    );
    assert!(
        diagnostics[1]["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert_eq!(diagnostics[1]["params"]["version"], 2);
}

#[test]
fn unsaved_dependencies_revalidate_open_importers() {
    let dep = "file:///tmp/lof-lsp-import/dep.lof";
    let root = "file:///tmp/lof-lsp-import/main.lof";
    let responses = conversation(vec![
        initialize(),
        open(dep, "export let value=#0;"),
        open(root, "import \"dep.lof\" as D; export let value=D::value;"),
        change(dep, "export let renamed=#0;"),
    ]);
    let root_diagnostics: Vec<_> = responses
        .iter()
        .filter(|r| r["method"] == "textDocument/publishDiagnostics" && r["params"]["uri"] == root)
        .collect();
    assert!(
        root_diagnostics[0]["params"]["diagnostics"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    assert!(
        root_diagnostics.last().unwrap()["params"]["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("D::value")
    );
}

#[test]
fn qualified_completions_work_in_incomplete_documents_without_duplicating_the_alias() {
    let uri = "file:///tmp/lof-lsp-complete/main.lof";
    let dep = "file:///tmp/lof-lsp-complete/dep.lof";
    let source = "import \"dep.lof\" as D;\nexport let value=D::v";
    let responses = conversation(vec![
        initialize(),
        open(dep, "let private=#0; export let value=#0;"),
        open(uri, source),
        json!({"id":9,"method":"textDocument/completion","params":{
            "textDocument":{"uri":uri},"position":text::position(source,source.len())}}),
    ]);
    let completion = responses.iter().find(|r| r["id"] == 9).unwrap();
    let items = completion["result"].as_array().unwrap();
    assert_eq!(items.len(), 1);
    assert_eq!(items[0]["label"], "value");
    assert_eq!(items[0]["textEdit"]["newText"], "value");
    assert_eq!(
        items[0]["textEdit"]["range"]["start"],
        text::position(source, source.len() - 1)
    );
}

#[test]
fn utf16_positions_and_file_uris_handle_unicode_and_spaces() {
    let source = "λ𝔸\nx";
    assert_eq!(
        text::position(source, "λ𝔸".len()),
        json!({"line":0,"character":3})
    );
    assert_eq!(
        text::offset(source, &json!({"line":0,"character":3})),
        "λ𝔸".len()
    );
    assert_eq!(
        text::offset(source, &json!({"line":1,"character":1})),
        source.len()
    );
    assert_eq!(
        text::file_path("file:///tmp/a%20b/%CE%BB.lof").unwrap(),
        std::path::PathBuf::from("/tmp/a b/λ.lof")
    );
    assert!(text::file_path("file://remote/a.lof").is_none());
    assert!(text::file_path("file:///tmp/%GG").is_none());
}

#[test]
fn framing_uses_utf8_bytes_and_rejects_missing_content_lengths() {
    let value = json!({"text":"λ𝔸"});
    let mut bytes = Vec::new();
    protocol::write(&mut bytes, &value).unwrap();
    assert_eq!(
        protocol::read(&mut Cursor::new(bytes)).unwrap(),
        Some(value)
    );
    assert!(
        protocol::read(&mut Cursor::new(
            b"Content-Type: application/json\r\n\r\n{}"
        ))
        .is_err()
    );
}
