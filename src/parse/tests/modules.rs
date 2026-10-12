use super::super::*;

#[test]
fn module_declarations_comments_and_qualified_names_parse() {
    let module = parse_module("// library\nimport \"../nat.lof\" as Nat; let private=#0; export let value=Nat::add(#1,#2);").unwrap();
    assert_eq!(module.imports[0].alias, "Nat");
    assert!(!module.definitions[0].exported);
    assert!(module.definitions[1].exported);
    assert!(parse_module("").unwrap().definitions.is_empty());
    assert!(parse("λx.x // comment at EOF").is_ok());
}

#[test]
fn module_syntax_rejects_missing_semicolons_and_misplaced_imports() {
    for source in [
        "export let value=#0",
        "let value=#0\nlet next=#1;",
        "import \"x.lof\" as X",
        "let value=#0; import \"x.lof\" as X;",
        "export import \"x.lof\" as X;",
        "#0",
        "import \"unfinished as X;",
    ] {
        assert!(parse_module(source).is_err(), "accepted {source}");
    }
}
