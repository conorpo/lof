use super::super::{parse, parse_core};
use crate::core::{
    kernel::{Context, check, infer, normalize},
    terms::Term,
};

#[test]
fn typed_binders_parse_infer_and_preserve_annotation_precedence() {
    let identity = parse_core("λ(A:U0).λ(x:A).x", &[]).unwrap();
    assert_eq!(
        identity,
        Term::typed_lam(Term::u(0), Term::typed_lam(Term::var(0), Term::var(0)))
    );
    assert_eq!(
        infer(&Context::new(), &identity).unwrap(),
        Term::pi(Term::u(0), Term::pi(Term::var(0), Term::var(1)))
    );
    let annotated = parse_core("λ(x:Nat).x : Nat -> Nat", &[]).unwrap();
    assert_eq!(
        annotated,
        Term::ann(
            Term::typed_lam(Term::nat(), Term::var(0)),
            Term::pi(Term::nat(), Term::nat())
        )
    );
    let application = parse_core("(λ(x:Nat).Succ(x))(#2)", &[]).unwrap();
    check(&Context::new(), &application, &Term::nat()).unwrap();
    assert_eq!(normalize(&application), Term::from(3));
}

#[test]
fn annotations_resolve_before_their_binder_and_keep_captured_let_scopes() {
    assert_eq!(
        parse_core("λ(A:U0).λ(A:A).A", &[]).unwrap(),
        Term::typed_lam(Term::u(0), Term::typed_lam(Term::var(0), Term::var(0)))
    );
    assert_eq!(
        parse_core("let T=A; λ(A:U0).λ(x:T).x", &["A"]).unwrap(),
        Term::typed_lam(Term::u(0), Term::typed_lam(Term::var(1), Term::var(0)))
    );
    assert!(parse_core("λ(x:x).x", &[]).is_err());
    for source in ["λ(x:).x", "λ(x Nat).x", "λ(x:Nat)x", "λx:Nat.x"] {
        assert!(parse(source).is_err(), "accepted {source}");
    }
}
