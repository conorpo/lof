use crate::{
    core::terms::{GlobalId, Term},
    parse::{parse, parse_core},
};
use std::collections::BTreeMap;

#[test]
fn printed_notation_preserves_binder_depths_and_operator_precedence() {
    for source in [
        "λ(A:U0).λ(x:A).refl(x)",
        "Π(A:U0).Σ(x:A).x=x",
        "λA.λx.λy.(x,(y,A))",
        "(λx.x : Nat -> Nat)(#2)",
        "λx.(x : Nat)",
        "¬¬Nat",
        "¬(Nat+1)",
        "¬(Nat->Nat)",
        "(¬Nat)+Nat",
        "(Nat+1)+0",
        "Nat+(1+0)",
        "(Nat=Nat)=(Nat=Nat)",
        "Σ(A:U0).Π(x:A).A",
        "Nat*(Nat->Nat)",
        "(λx.λy.x)(#2)(#3)",
        "ind_nat(λn.Nat,#0,λn.λr.Succ(r))",
        "ind_Σ(Nat*Nat,λp.Nat,λa.λb.a)((#2,#3))",
        "ind_coproduct(Nat+1,λs.Nat,λn.n,λu.#0)(inl(#2))",
        "ind_coproduct(Nat+1,λs.Nat,λn.n,λu.#0)(inr(*))",
        "ind_id(Nat,λx.λy.λp.Nat,λx.x)(#2,#2,refl(#2))",
        "ind0(λx.Nat)",
        "ind1(λx.Nat,#2)(*)",
        "#255",
        "Succ(#255)",
        "λn.Succ(n)",
        "U12",
    ] {
        let term = parse_core(source, &[]).unwrap();
        let printed = term.to_string();
        assert_eq!(
            parse_core(&printed, &[]).unwrap(),
            term,
            "{source} printed as {printed}"
        );
    }
}

#[test]
fn negation_and_unicode_binders_have_compact_readable_output() {
    for (source, expected) in [
        ("(Nat -> 0) -> 0", "¬¬Nat"),
        ("(Nat -> Nat) -> 0", "¬(Π(x:Nat). Nat)"),
        ("Π(A:U0).Σ(x:A).x=x", "Π(x:U0). Σ(y:x). y = y"),
        ("λ(A:U0).λ(x:A).x", "λ(x:U0). λ(y:x). y"),
        ("(*,#3)", "(*, #3)"),
    ] {
        assert_eq!(parse_core(source, &[]).unwrap().to_string(), expected);
    }
}

#[test]
fn module_names_are_unambiguous_and_generated_binders_do_not_capture_constants() {
    let id = GlobalId::new("/library.lof::identity");
    let names = BTreeMap::from([
        ("Functions::identity".to_owned(), id.clone()),
        ("x".to_owned(), id.clone()),
    ]);
    let term = Term::lam(Term::app(Term::constant(id), Term::var(0)));
    let printed = term.display_with_names(&names).to_string();
    assert_eq!(printed, "λy. x(y)");
    assert_eq!(
        parse(&printed)
            .unwrap()
            .lower_with_globals(&[], &names)
            .unwrap(),
        term
    );
    assert_eq!(Term::lam(Term::var(1)).to_string(), "λx. @0");
}

#[test]
fn binder_letters_cycle_with_suffixes_without_shadowing_earlier_binders() {
    let term = (0..28).fold(Term::var(27), |body, _| Term::lam(body));
    let printed = term.to_string();
    assert!(printed.starts_with("λx. λy. λz. λa. λb. λc. "));
    assert!(printed.ends_with("λw. λx1. λy1. x"));
    assert_eq!(parse_core(&printed, &[]).unwrap(), term);
}
