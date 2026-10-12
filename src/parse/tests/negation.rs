use crate::{core::terms::Term, parse::parse_core};

#[test]
fn negation_binds_tightly_and_preserves_anonymous_binder_depths() {
    for (source, expanded) in [
        ("¬A", "A -> 0"),
        ("¬¬A", "(A -> 0) -> 0"),
        ("¬A -> B", "(A -> 0) -> B"),
        ("¬(A -> B)", "(A -> B) -> 0"),
        ("¬P(x)", "P(x) -> 0"),
        ("¬A * B", "(A -> 0) * B"),
        ("λ(A:U0).¬A", "λ(A:U0).A -> 0"),
    ] {
        assert_eq!(
            parse_core(source, &["A", "B", "P", "x"]).unwrap(),
            parse_core(expanded, &["A", "B", "P", "x"]).unwrap(),
            "{source}"
        );
    }
    assert_eq!(
        parse_core("1 → 0", &[]).unwrap(),
        Term::pi(Term::unit(), Term::empty())
    );
    assert!(parse_core("¬", &[]).is_err());
}
