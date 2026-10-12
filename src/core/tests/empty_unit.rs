use super::super::{Context, check, infer, normalize};
use crate::core::terms::Term;

#[test]
fn empty_and_unit_form_small_types_and_only_unit_has_a_constructor() {
    let context = Context::new();
    for ty in [Term::empty(), Term::unit()] {
        assert_eq!(infer(&context, &ty).unwrap(), Term::u(0));
    }
    assert_eq!(infer(&context, &Term::tt()).unwrap(), Term::unit());
    assert!(check(&context, &Term::tt(), &Term::empty()).is_err());
    assert!(check(&context, &Term::zero(), &Term::empty()).is_err());
    assert!(check(&context, &Term::zero(), &Term::unit()).is_err());
}

#[test]
fn empty_elimination_has_a_dependent_result_and_stays_neutral() {
    let eliminator = Term::ind_empty(Term::lam(Term::id(Term::var(0), Term::var(0))));
    let expected = Term::pi(Term::empty(), Term::id(Term::var(0), Term::var(0)));
    check(&Context::new(), &eliminator, &expected).unwrap();
    let mut context = Context::new();
    context.assume(Term::empty()).unwrap();
    let application = Term::app(eliminator, Term::var(0));
    check(
        &context,
        &application,
        &Term::id(Term::var(0), Term::var(0)),
    )
    .unwrap();
    assert_eq!(normalize(&application), application);
    assert!(infer(&Context::new(), &Term::ind_empty(Term::lam(Term::zero()))).is_err());
}

#[test]
fn unit_elimination_checks_a_dependent_case_and_computes() {
    let family = Term::lam(Term::id(Term::var(0), Term::tt()));
    let eliminator = Term::ind_unit(family.clone(), Term::refl(Term::tt()));
    check(
        &Context::new(),
        &eliminator,
        &Term::pi(Term::unit(), Term::id(Term::var(0), Term::tt())),
    )
    .unwrap();
    let application = Term::app(eliminator.clone(), Term::tt());
    check(
        &Context::new(),
        &application,
        &Term::id(Term::tt(), Term::tt()),
    )
    .unwrap();
    assert_eq!(normalize(&application), Term::refl(Term::tt()));
    let mut context = Context::new();
    context.assume(Term::unit()).unwrap();
    let neutral = Term::app(eliminator, Term::var(0));
    check(&context, &neutral, &Term::id(Term::var(0), Term::tt())).unwrap();
    assert_eq!(normalize(&neutral), neutral); // No judgmental unit eta rule.
    assert!(infer(&Context::new(), &Term::ind_unit(family, Term::zero())).is_err());
}

#[test]
fn substitution_through_empty_and_unit_eliminators_preserves_outer_binders() {
    // (λC. λc. ind1(λu.C,c)) Nat 3 tt : Nat
    let function = Term::ann(
        Term::lam(Term::lam(Term::ind_unit(
            Term::lam(Term::var(2)),
            Term::var(0),
        ))),
        Term::pi(
            Term::u(0),
            Term::pi(Term::var(0), Term::pi(Term::unit(), Term::var(2))),
        ),
    );
    let application = Term::app(
        Term::app(Term::app(function, Term::nat()), Term::from(3)),
        Term::tt(),
    );
    check(&Context::new(), &application, &Term::nat()).unwrap();
    assert_eq!(normalize(&application), Term::from(3));

    let function = Term::ann(
        Term::lam(Term::ind_empty(Term::lam(Term::var(1)))),
        Term::pi(Term::u(0), Term::pi(Term::empty(), Term::var(1))),
    );
    let applied = Term::app(function, Term::nat());
    check(
        &Context::new(),
        &applied,
        &Term::pi(Term::empty(), Term::nat()),
    )
    .unwrap();
    assert_eq!(normalize(&applied), Term::ind_empty(Term::lam(Term::nat())));
}
