"use strict";

const vscode = require("vscode");
const { spawn } = require("node:child_process");
const path = require("node:path");
let active;

// The server uses only diagnostics, full document sync, and completion. Keep
// this local connector dependency-free; stdout is reserved for framed JSON-RPC.
class Client {
  constructor(output, diagnostics) {
    this.output = output;
    this.diagnostics = diagnostics;
    this.pending = new Map();
    this.open = new Map();
    this.sequence = 0;
    this.buffer = Buffer.alloc(0);
    this.stopped = false;
  }

  async start() {
    const workspace = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    let executable = vscode.workspace.getConfiguration("lof").get("serverPath");
    if (executable.includes("${workspaceFolder}")) {
      if (!workspace) throw new Error("Open the LOF project folder or set lof.serverPath.");
      executable = executable.replaceAll("${workspaceFolder}", workspace);
    }
    if (!path.isAbsolute(executable) && workspace) executable = path.resolve(workspace, executable);
    this.process = spawn(executable, [], { cwd: workspace, stdio: "pipe" });
    this.process.stdout.on("data", bytes => this.receive(bytes));
    this.process.stderr.on("data", bytes => this.output.append(bytes.toString()));
    this.process.stdin.on("error", error => this.fail(error));
    this.process.on("error", error => this.fail(error));
    this.process.on("exit", (code, signal) => {
      this.fail(new Error(`lof-lsp exited (${signal || code}).`));
    });
    await this.request("initialize", {
      processId: process.pid, rootUri: vscode.workspace.workspaceFolders?.[0]?.uri.toString() || null,
      capabilities: { general: { positionEncodings: ["utf-16"] } }
    });
    this.notify("initialized", {});
    this.ready = true;
    for (const document of vscode.workspace.textDocuments) this.sync(document);
    this.output.appendLine(`LOF server ready: ${executable}`);
  }

  send(message) {
    if (this.stopped) throw new Error("LOF server is stopped.");
    const bytes = Buffer.from(JSON.stringify({ jsonrpc: "2.0", ...message }), "utf8");
    this.process.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${bytes.length}\r\n\r\n`), bytes]));
  }

  notify(method, params) {
    if (!this.stopped) this.send({ method, params });
  }

  request(method, params) {
    const id = ++this.sequence;
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`LOF request timed out: ${method}`));
      }, 30000);
      this.pending.set(id, { resolve, reject, timer });
      try { this.send({ id, method, params }); }
      catch (error) { clearTimeout(timer); this.pending.delete(id); reject(error); }
    });
  }

  receive(bytes) {
    this.buffer = Buffer.concat([this.buffer, bytes]);
    try {
      while (true) {
        const boundary = this.buffer.indexOf("\r\n\r\n");
        if (boundary < 0) {
          if (this.buffer.length > 8192) throw new Error("LOF response header is too large.");
          return;
        }
        const length = /^Content-Length:\s*(\d+)$/im.exec(this.buffer.subarray(0, boundary).toString());
        if (!length || Number(length[1]) > 16777216) throw new Error("Invalid LOF response framing.");
        const end = boundary + 4 + Number(length[1]);
        if (this.buffer.length < end) return;
        const message = JSON.parse(this.buffer.subarray(boundary + 4, end).toString("utf8"));
        this.buffer = this.buffer.subarray(end);
        if (Object.hasOwn(message, "id") && this.pending.has(message.id)) {
          const pending = this.pending.get(message.id);
          this.pending.delete(message.id);
          clearTimeout(pending.timer);
          if (message.error) pending.reject(new Error(message.error.message));
          else pending.resolve(message.result);
        } else if (message.method === "textDocument/publishDiagnostics") {
          this.publish(message.params);
        }
      }
    } catch (error) { this.fail(error); this.process.kill(); }
  }

  publish({ uri, version, diagnostics }) {
    const document = vscode.workspace.textDocuments.find(item => item.uri.toString() === uri);
    if (document && version !== undefined && document.version !== version) return;
    this.diagnostics.set(vscode.Uri.parse(uri), diagnostics.map(item => {
      const diagnostic = new vscode.Diagnostic(toRange(item.range), item.message,
        item.severity === 2 ? vscode.DiagnosticSeverity.Warning : vscode.DiagnosticSeverity.Error);
      diagnostic.source = "lof";
      return diagnostic;
    }));
  }

  sync(document) {
    if (!this.ready || this.stopped || document.languageId !== "lof" || document.uri.scheme !== "file") return;
    const uri = document.uri.toString();
    if (!this.open.has(uri)) {
      this.notify("textDocument/didOpen", { textDocument: {
        uri, languageId: "lof", version: document.version, text: document.getText()
      }});
    } else if (this.open.get(uri) !== document.version) {
      this.notify("textDocument/didChange", {
        textDocument: { uri, version: document.version }, contentChanges: [{ text: document.getText() }]
      });
    }
    this.open.set(uri, document.version);
  }

  close(document) {
    const uri = document.uri.toString();
    if (this.open.delete(uri)) this.notify("textDocument/didClose", { textDocument: { uri } });
  }

  async complete(document, position, token) {
    if (!this.ready || this.stopped) return [];
    this.sync(document);
    try {
      const result = await this.request("textDocument/completion", {
        textDocument: { uri: document.uri.toString() }, position: { line: position.line, character: position.character }
      });
      if (token.isCancellationRequested) return [];
      return (result || []).map(item => {
        const completion = new vscode.CompletionItem(item.label, vscode.CompletionItemKind.Variable);
        completion.detail = item.detail;
        if (item.textEdit) {
          completion.range = toRange(item.textEdit.range);
          completion.insertText = item.textEdit.newText;
        }
        return completion;
      });
    } catch (error) { this.output.appendLine(error.message); return []; }
  }

  fail(error) {
    if (!this.stopped) this.output.appendLine(error.message);
    this.ready = false;
    for (const pending of this.pending.values()) {
      clearTimeout(pending.timer);
      pending.reject(error);
    }
    this.pending.clear();
  }

  async stop() {
    if (this.stopped) return;
    if (this.ready) {
      try { await this.request("shutdown", null); this.notify("exit", null); }
      catch (_) { /* The process may already have exited. */ }
    }
    this.stopped = true;
    this.fail(new Error("LOF server stopped."));
    this.process?.kill();
    this.diagnostics.clear();
  }
}

function toRange(range) {
  return new vscode.Range(range.start.line, range.start.character, range.end.line, range.end.character);
}

async function activate(context) {
  const output = vscode.window.createOutputChannel("LOF Language Server");
  const diagnostics = vscode.languages.createDiagnosticCollection("lof");
  const restart = async () => {
    if (active) await active.stop();
    active = new Client(output, diagnostics);
    try { await active.start(); }
    catch (error) {
      output.appendLine(error.message);
      await active.stop();
      vscode.window.showErrorMessage(`LOF: ${error.message} Build lof-lsp and check lof.serverPath.`);
    }
  };
  context.subscriptions.push(output, diagnostics,
    vscode.commands.registerCommand("lof.restartServer", restart),
    vscode.workspace.onDidOpenTextDocument(document => active?.sync(document)),
    vscode.workspace.onDidChangeTextDocument(event => active?.sync(event.document)),
    vscode.workspace.onDidCloseTextDocument(document => active?.close(document)),
    vscode.workspace.onDidChangeConfiguration(event => { if (event.affectsConfiguration("lof.serverPath")) restart(); }),
    vscode.languages.registerCompletionItemProvider({ language: "lof", scheme: "file" }, {
      provideCompletionItems: (document, position, token) => active?.complete(document, position, token)
    }, ":")
  );
  const watcher = vscode.workspace.createFileSystemWatcher("**/*.lof");
  const changed = (uri, type) => {
    if (active?.ready) active.notify("workspace/didChangeWatchedFiles", { changes: [{ uri: uri.toString(), type }] });
  };
  context.subscriptions.push(watcher, watcher.onDidCreate(uri => changed(uri, 1)),
    watcher.onDidChange(uri => changed(uri, 2)), watcher.onDidDelete(uri => changed(uri, 3)));
  await restart();
}

async function deactivate() { await active?.stop(); }
module.exports = { activate, deactivate };
