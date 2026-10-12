use super::super::*;
use crate::core::{
    kernel::{Context, check, normalize},
    terms::Term,
};

#[test]
fn nondependent_recursors_check_and_compute_through_core_eliminators() {
    for (source, expected) in [
        ("recNat(Nat,#0,λn.λr.Succ(r))(#3)", Term::from(3)),
        ("rec_Σ(Nat*Nat,Nat,λa.λb.a)((#2,#3))", Term::from(2)),
        (
            "recCoproduct(Nat+Nat,Nat,λa.a,λb.Succ(b))(inr(#2))",
            Term::from(3),
        ),
        ("recId(Nat,Nat,λa.Succ(a))(#2,#2,refl(#2))", Term::from(3)),
        ("rec1(Nat,#3)(tt)", Term::from(3)),
    ] {
        let term = parse_core(source, &[]).unwrap();
        check(&Context::new(), &term, &Term::nat()).unwrap();
        assert_eq!(normalize(&term), expected);
    }
}

#[test]
fn empty_and_unit_surface_syntax_checks_dependent_and_constant_motives() {
    for (source, expected) in [
        ("0", Term::u(0)),
        ("1", Term::u(0)),
        ("*", Term::unit()),
        ("rec0(Nat)", Term::pi(Term::empty(), Term::nat())),
        (
            "ind0(λx.x=x)",
            Term::pi(Term::empty(), Term::id(Term::var(0), Term::var(0))),
        ),
        ("ind1(λx.x=*,refl(*))(*)", Term::id(Term::tt(), Term::tt())),
        (
            "λA.rec0(A)",
            Term::pi(Term::u(0), Term::pi(Term::empty(), Term::var(1))),
        ),
    ] {
        check(
            &Context::new(),
            &parse_core(source, &[]).unwrap(),
            &expected,
        )
        .unwrap();
    }
    assert_eq!(
        parse_core("rec0(C)", &["C"]).unwrap(),
        Term::ind_empty(Term::lam(Term::var(1)))
    );
    assert_eq!(
        parse_core("rec1(C,c)", &["C", "c"]).unwrap(),
        Term::ind_unit(Term::lam(Term::var(2)), Term::var(0))
    );
    for source in ["ind0()", "ind0(P,x)", "ind1(P)", "rec0()", "rec1(C,c,x)"] {
        assert!(parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn constant_motives_weaken_surrounding_variables_without_capture() {
    let names = &["C", "z", "s"];
    assert_eq!(
        parse_core("recNat(C,z,s)", names).unwrap(),
        Term::ind_nat(Term::lam(Term::var(3)), Term::var(1), Term::var(0))
    );
    assert_eq!(
        parse_core("recId(C,z,s)", names).unwrap(),
        Term::ind_id(
            Term::var(2),
            Term::lam(Term::lam(Term::lam(Term::var(4)))),
            Term::var(0)
        )
    );
    assert!(
        check(
            &Context::new(),
            &parse_core("recNat(#0,#0,λn.λr.r)(#0)", &[]).unwrap(),
            &Term::nat()
        )
        .is_err()
    );
}
