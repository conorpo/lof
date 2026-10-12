fn main() {
    let input = std::io::stdin();
    let output = std::io::stdout();
    match lof::lsp::run(input.lock(), output.lock()) {
        Ok(status) => std::process::exit(status),
        Err(error) => {
            eprintln!("lof-lsp: {error}");
            std::process::exit(1);
        }
    }
}
