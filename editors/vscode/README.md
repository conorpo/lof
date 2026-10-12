# LOF for VS Code / Code OSS

Build the server from the LOF repository:

```sh
cargo +nightly build --bin lof-lsp
```

The connector starts `target/debug/lof-lsp` in the open workspace. Set
`lof.serverPath` to an absolute binary path when working in another folder.
Use **LOF: Restart Language Server** after rebuilding the binary. Logs appear
in the **LOF Language Server** output channel.

For local development, link this directory into your editor's extension directory
as `lof-local.lof-language-0.1.0`. Code OSS on Linux uses
`~/.vscode-oss/extensions`; Microsoft's VS Code uses `~/.vscode/extensions`.
Reload the editor window after linking. Alternatively launch an extension host:

```sh
code --extensionDevelopmentPath=/absolute/path/to/lof/editors/vscode /absolute/path/to/lof
```

Open `src/defined/arithmetic/arithmetic.lof` and add `export let bad = #0 : U0;`
to see a diagnostic. In a new `.lof` file next to it, try:

```text
import "./arithmetic.lof" as Arithmetic;
export let example = Arithmetic::add(#2,#3);
```

Completion after `Arithmetic::` offers `add` and `mul`. Changes to open imported
files are checked before they are saved. Module declarations require semicolons.

Initial features: syntax highlighting, module diagnostics, global and imported
name completion. Diagnostics stop at the first error in each open module. Local
binder completion, hover, go-to-definition, rename, formatting, and embedded LOF
inside Rust strings are not implemented. Full documents are rechecked on edits;
checking is synchronous, with no cancellation or normalization resource limit.

## Math input

The extension provides snippets `\neg`, `\lambda`, `\Pi`, `\Sigma`, `\to`, and
`\times`. Invoke completion with Ctrl+Space and select the symbol. Reload the
editor window after installing updated snippet or grammar contributions.

On this machine, Right Alt is already Compose (`compose:ralt`). Tap and release
Right Alt, then enter the sequence; do not hold it as a modifier:

| Sequence | Symbol |
| --- | --- |
| `- ,` | `¬` |
| `- >` / `< -` | `→` / `←` |
| `= >` | `⇒` |
| `x x` | `×` |
| `g l` / `g P` / `g S` | `λ` / `Π` / `Σ` |

The Greek sequences are in `~/.XCompose`; the other sequences are supplied by
its `include "%L"`. These bindings work in applications that honor Compose.
LOF accepts `→` and `×`; `←` and `⇒` are useful for prose but are not LOF operators.
