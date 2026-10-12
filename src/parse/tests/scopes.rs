use super::super::*;
use crate::core::terms::Term;

#[test]
fn expands_let_values_and_supports_compact_lambdas() {
    assert_eq!(
        parse_core("{ let x = λx.refl_x; x }", &[]).unwrap(),
        Term::lam(Term::refl(Term::var(0))),
    );
    assert_eq!(
        parse_core("let id = λ(x). x; id", &[]).unwrap(),
        Term::lam(Term::var(0)),
    );
    assert_eq!(parse_core("{ #2; }", &[]).unwrap(), Term::from(2));
}

#[test]
fn annotates_the_entire_bound_lambda() {
    assert_eq!(
        parse_core("{ let x = λx.refl_x : Π(a:A). a=a; x }", &["A"]).unwrap(),
        Term::ann(
            Term::lam(Term::refl(Term::var(0))),
            Term::pi(Term::var(0), Term::id(Term::var(0), Term::var(0))),
        ),
    );
    assert_eq!(
        parse_core("let id = λx.x : Nat -> Nat; id(#2)", &[]).unwrap(),
        Term::app(
            Term::ann(Term::lam(Term::var(0)), Term::pi(Term::nat(), Term::nat())),
            Term::from(2),
        ),
    );
}

#[test]
fn blocks_are_expressions_in_applications_and_arguments() {
    let identity = Term::ann(Term::lam(Term::var(0)), Term::pi(Term::nat(), Term::nat()));
    assert_eq!(
        parse_core("{ let id = λx.x : Nat -> Nat; id }({ let n=#2; n })", &[]).unwrap(),
        Term::app(identity, Term::from(2)),
    );
}

#[test]
fn nearest_variable_or_definition_shadows_outer_names() {
    assert_eq!(
        parse_core("let x=#0; λx.x", &[]).unwrap(),
        Term::lam(Term::var(0)),
    );
    assert_eq!(
        parse_core("λx.{ let x=#1; x }", &[]).unwrap(),
        Term::lam(Term::from(1)),
    );
    assert_eq!(
        parse_core("let A=Nat; Π(A:U0). A", &[]).unwrap(),
        Term::pi(Term::u(0), Term::var(0)),
    );
}

#[test]
fn nested_blocks_restore_outer_definitions() {
    assert_eq!(
        parse_core("let x=#0; ({ let x=#1; x }, x)", &[]).unwrap(),
        Term::pair(Term::from(1), Term::zero()),
    );
    assert_eq!(
        parse_core("({ let x=#0; x }, x)", &[]),
        Err(FrontendError::Resolve(ResolveError { name: "x".into() })),
    );
}

#[test]
fn definitions_capture_the_earlier_definition_environment() {
    assert_eq!(
        parse_core("let x=#0; let f=λy.x; let x=#1; f", &[]).unwrap(),
        Term::lam(Term::zero()),
    );
    assert_eq!(
        parse_core("let y=#0; let x=y; let y=#1; x", &[]).unwrap(),
        Term::zero(),
    );
}

#[test]
fn let_is_nonrecursive_and_rhs_can_see_the_previous_binding() {
    assert_eq!(
        parse_core("let x=#0; let x=Succ(x); x", &[]).unwrap(),
        Term::succ(Term::zero()),
    );
    assert_eq!(parse_core("let x=x; x", &["x"]).unwrap(), Term::var(0),);
    for source in [
        "let x=x; x",
        "let x=y; let y=#0; x",
        "let unused=missing; #0",
    ] {
        assert!(matches!(
            parse_core(source, &[]),
            Err(FrontendError::Resolve(_))
        ));
    }
}

#[test]
fn expansion_preserves_captured_bound_variables() {
    assert_eq!(
        parse_core("λx.{ let y=x; λx.y }", &[]).unwrap(),
        Term::lam(Term::lam(Term::var(1))),
    );
    assert_eq!(
        parse_core("λx.{ let T=x; Σ(x:T). T }", &[]).unwrap(),
        Term::lam(Term::sigma(Term::var(0), Term::var(1))),
    );
}

#[test]
fn expansion_cannot_capture_external_variables() {
    assert_eq!(
        parse_core("let y=x; λx.y", &["x"]).unwrap(),
        Term::lam(Term::var(1)),
    );
    assert_eq!(
        parse_core("let f=λz.(z,x); λx.f", &["x"]).unwrap(),
        Term::lam(Term::lam(Term::pair(Term::var(0), Term::var(2)))),
    );
}

#[test]
fn anonymous_binders_and_annotations_preserve_definition_scope() {
    assert_eq!(
        parse_core("let T=A; Nat -> T*T", &["A"]).unwrap(),
        Term::pi(Term::nat(), Term::sigma(Term::var(1), Term::var(2))),
    );
    assert_eq!(
        parse_core("let f=λx.x : A -> A; λA.f", &["A"]).unwrap(),
        Term::lam(Term::ann(
            Term::lam(Term::var(0)),
            Term::pi(Term::var(1), Term::var(2)),
        )),
    );
}

#[test]
fn newline_separators_allow_multiline_values() {
    assert_eq!(
        parse_core("let id = λx.\n x :\n Nat -> Nat\nlet copy = id\ncopy", &[]).unwrap(),
        Term::ann(Term::lam(Term::var(0)), Term::pi(Term::nat(), Term::nat())),
    );
    assert_eq!(
        parse_core("{\nlet x=#0\nlet y=Succ(x)\ny\n}", &[]).unwrap(),
        Term::succ(Term::zero()),
    );
}

#[test]
fn identity_and_reflexivity_syntax_preserves_binders() {
    assert_eq!(
        parse_core("λx.refl(x)", &[]).unwrap(),
        parse_core("λx.refl_x", &[]).unwrap(),
    );
    assert_eq!(
        parse_core("a=a -> a=a", &["a"]).unwrap(),
        Term::pi(
            Term::id(Term::var(0), Term::var(0)),
            Term::id(Term::var(1), Term::var(1)),
        ),
    );
    assert_eq!(
        parse_core("λx.(x : A)", &["A"]).unwrap(),
        Term::lam(Term::ann(Term::var(0), Term::var(1))),
    );
}

#[test]
fn malformed_scopes_and_identity_syntax_report_parse_errors() {
    for source in [
        "{}",
        "{ let x=#0; }",
        "{ let x=#0 x }",
        "{ #0; #1 }",
        "let =#0; #0",
        "let x=; x",
        "{ let x=#0; x",
        "let x=#0; x }",
        "a=b=c",
        "refl()",
        "refl(a,b)",
    ] {
        assert!(parse(source).is_err(), "unexpectedly accepted {source}");
    }
    let error = parse("{ let x #0; x }").unwrap_err();
    assert_eq!(error.offset, 8);
}
