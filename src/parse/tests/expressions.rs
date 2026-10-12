use super::super::*;
use crate::core::kernel::{Context, check, infer, normalize};
use crate::core::terms::Term;

#[test]
fn parses_requested_syntax_with_free_name() {
    let source = "Π(A: U0). (Σ(x:A). P(x)) -> A*A";
    let expression = parse(source).unwrap();
    assert_eq!(
        expression.lower(&[]),
        Err(ResolveError {
            name: "P".to_owned()
        })
    );
    assert_eq!(
        parse_core(source, &["P"]).unwrap(),
        Term::pi(
            Term::u(0),
            Term::pi(
                Term::sigma(Term::var(0), Term::app(Term::var(2), Term::var(0))),
                Term::sigma(Term::var(1), Term::var(2)),
            ),
        )
    );
}

#[test]
fn precedence_and_anonymous_binders_are_correct() {
    assert_eq!(
        parse_core("A*B -> C -> D", &["A", "B", "C", "D"]).unwrap(),
        Term::pi(
            Term::sigma(Term::var(3), Term::var(3)),
            Term::pi(Term::var(2), Term::var(2)),
        )
    );
    assert_eq!(
        parse_core("Π(A: U0). Π(A: U0). A", &[]).unwrap(),
        Term::pi(Term::u(0), Term::pi(Term::u(0), Term::var(0)))
    );
}

#[test]
fn parsed_terms_can_be_checked() {
    let ty = parse_core("Π(A: U0). A -> A*A", &[]).unwrap();
    let duplicate = parse_core("λ(A). λ(x). (x,x)", &[]).unwrap();
    check(&Context::new(), &duplicate, &ty).unwrap();
}

#[test]
fn resolves_and_checks_explicit_polymorphic_predicate() {
    let mut context = Context::new();
    // P : Π(T : U0). T -> U0
    context
        .assume(Term::pi(Term::u(0), Term::pi(Term::var(0), Term::u(0))))
        .unwrap();
    let ty = parse_core("Π(A: U0). (Σ(x:A). P(A,x)) -> A*A", &["P"]).unwrap();
    assert_eq!(infer(&context, &ty).unwrap(), Term::u(1));
}

#[test]
fn rejects_bad_syntax_and_reports_offsets() {
    let error = parse("Π(A U0). A").unwrap_err();
    assert_eq!(error.offset, 5);
    assert!(parse("A ->").is_err());
    assert!(parse("P()").is_err());
    assert!(parse("A B").is_err());
}

#[test]
fn accepts_unicode_type_formers_and_annotation() {
    assert_eq!(
        parse_core("Π(A: U0). A × A", &[]).unwrap(),
        Term::pi(Term::u(0), Term::sigma(Term::var(0), Term::var(1)))
    );
    assert_eq!(
        parse_core("(λ(x). x) : (A -> A)", &["A"]).unwrap(),
        Term::ann(
            Term::lam(Term::var(0)),
            Term::pi(Term::var(0), Term::var(1))
        )
    );
    assert_eq!(
        parse_core("A -> A : U0", &["A"]).unwrap(),
        Term::ann(Term::pi(Term::var(0), Term::var(1)), Term::u(0))
    );
}

#[test]
fn annotations_check_and_compute() {
    let identity = parse_core("(λ(n). n) : (Nat -> Nat)", &[]).unwrap();
    let context = Context::new();
    assert_eq!(
        infer(&context, &identity).unwrap(),
        Term::pi(Term::nat(), Term::nat())
    );
    let application = Term::app(identity, Term::from(3));
    check(&context, &application, &Term::nat()).unwrap();
    assert_eq!(normalize(&application), Term::from(3));
}

#[test]
fn parses_natural_number_constructors_and_u8_literals() {
    for (source, expected) in [
        ("Nat", Term::nat()),
        ("Zero", Term::zero()),
        ("#0", Term::zero()),
        ("0", Term::empty()),
        ("1", Term::unit()),
        ("*", Term::tt()),
        ("1*1", Term::sigma(Term::unit(), Term::unit())),
        (
            "(*,*) : 1*1",
            Term::ann(
                Term::pair(Term::tt(), Term::tt()),
                Term::sigma(Term::unit(), Term::unit()),
            ),
        ),
        ("Succ(#2)", Term::from(3)),
        ("#255", Term::from(u8::MAX)),
    ] {
        assert_eq!(parse_core(source, &[]).unwrap(), expected);
    }
    let error = parse("#256").unwrap_err();
    assert_eq!(error.offset, 0);
    assert!(error.message.contains("#255"));
    for source in ["2", "42", "01", "#", "#-1", "#256"] {
        assert!(parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn coproduct_precedence_and_associativity_are_correct() {
    assert_eq!(
        parse_core("Nat*Nat + Nat -> Nat + Nat", &[]).unwrap(),
        Term::pi(
            Term::coproduct(Term::sigma(Term::nat(), Term::nat()), Term::nat()),
            Term::coproduct(Term::nat(), Term::nat()),
        ),
    );
    assert_eq!(
        parse_core("Nat + Nat + Nat", &[]).unwrap(),
        Term::coproduct(Term::nat(), Term::coproduct(Term::nat(), Term::nat())),
    );
}

#[test]
fn eliminator_arguments_share_the_surrounding_scope() {
    let cases = [
        (
            "ind_Σ(S,P,c)",
            &["S", "P", "c"][..],
            Term::ind_sigma(Term::var(2), Term::var(1), Term::var(0)),
        ),
        (
            "ind_coproduct(C,P,l,r)",
            &["C", "P", "l", "r"][..],
            Term::ind_coproduct(Term::var(3), Term::var(2), Term::var(1), Term::var(0)),
        ),
        (
            "ind_nat(P,z,s)",
            &["P", "z", "s"][..],
            Term::ind_nat(Term::var(2), Term::var(1), Term::var(0)),
        ),
    ];
    for (source, names, expected) in cases {
        assert_eq!(parse_core(source, names).unwrap(), expected);
    }
}

#[test]
fn parsed_eliminators_type_check_and_reduce() {
    let cases = [
        ("ind_Σ(Nat*Nat, λ(p). Nat, λ(a). λ(b). a)((#2,#3))", 2),
        (
            "ind_coproduct(Nat+Nat, λ(p). Nat, λ(a). Succ(a), λ(b). b)(inl(#2))",
            3,
        ),
        (
            "ind_coproduct(Nat+Nat, λ(p). Nat, λ(a). Succ(a), λ(b). b)(inr(#2))",
            2,
        ),
        ("ind_nat(λ(n). Nat, #5, λ(n). λ(ih). Succ(Succ(ih)))(#2)", 9),
    ];
    for (source, expected) in cases {
        let term = parse_core(source, &[]).unwrap();
        check(&Context::new(), &term, &Term::nat()).unwrap();
        assert_eq!(normalize(&term), Term::from(expected));
    }
}

#[test]
fn parses_and_computes_hott_addition() {
    let source = "ind_nat(λ(n). Nat -> Nat, λ(m). m,
        λ(n). λ(g). λ(m). Succ(g(m)))(#2,#3)";
    let term = parse_core(source, &[]).unwrap();
    check(&Context::new(), &term, &Term::nat()).unwrap();
    assert_eq!(normalize(&term), Term::from(5));
}

#[test]
fn projections_can_be_defined_as_ordinary_named_functions() {
    assert_eq!(
        parse_core("λ(fst). fst(p)", &["p"]).unwrap(),
        Term::lam(Term::app(Term::var(0), Term::var(1))),
    );
    assert_eq!(
        parse_core("snd(p)", &["snd", "p"]).unwrap(),
        Term::app(Term::var(1), Term::var(0)),
    );
}

#[test]
fn rejects_wrong_constructor_arity() {
    for source in [
        "Succ()",
        "Succ(#0,#1)",
        "inl()",
        "inr(#0,#1)",
        "ind_Σ(S,P)",
        "ind_Σ(S,P,c,x)",
        "ind_coproduct(C,P,l)",
        "ind_coproduct(C,P,l,r,x)",
        "ind_nat(P,z)",
        "ind_nat(P,z,s,x)",
    ] {
        assert!(parse(source).is_err(), "unexpectedly accepted {source}");
    }
}
