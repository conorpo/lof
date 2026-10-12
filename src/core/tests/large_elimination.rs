use super::super::{Context, check, infer, normalize};
use crate::core::terms::Term;

#[test]
fn nat_elimination_builds_types_and_retains_typing_on_a_neutral_input() {
    // P(n) = U0 : U1, d = Nat : U0, s(n,T) = T : U0.
    let eliminator = Term::ind_nat(
        Term::lam(Term::u(0)),
        Term::nat(),
        Term::lam(Term::lam(Term::var(0))),
    );
    check(
        &Context::new(),
        &eliminator,
        &Term::pi(Term::nat(), Term::u(0)),
    )
    .unwrap();
    let application = Term::app(eliminator.clone(), Term::from(2));
    check(&Context::new(), &application, &Term::u(0)).unwrap();
    assert_eq!(normalize(&application), Term::nat());

    let mut context = Context::new();
    context.assume(Term::nat()).unwrap();
    let neutral = Term::app(eliminator, Term::var(0));
    check(&context, &neutral, &Term::u(0)).unwrap();
    // Its untyped normalized motive must still be recognized as large.
    let normal = normalize(&neutral);
    check(&context, &normal, &Term::u(0)).unwrap();
}

#[test]
fn all_eliminators_allow_motives_in_higher_universes() {
    let sigma = Term::sigma(Term::nat(), Term::nat());
    let coproduct = Term::coproduct(Term::nat(), Term::unit());
    let cases = [
        (
            Term::app(
                Term::ind_unit(Term::lam(Term::u(0)), Term::nat()),
                Term::tt(),
            ),
            Term::nat(),
        ),
        (
            Term::app(
                Term::ind_sigma(
                    sigma,
                    Term::lam(Term::u(0)),
                    Term::lam(Term::lam(Term::nat())),
                ),
                Term::pair(Term::zero(), Term::zero()),
            ),
            Term::nat(),
        ),
        (
            Term::app(
                Term::ind_coproduct(
                    coproduct,
                    Term::lam(Term::u(0)),
                    Term::lam(Term::nat()),
                    Term::lam(Term::unit()),
                ),
                Term::inr(Term::tt()),
            ),
            Term::unit(),
        ),
        (
            Term::app(
                Term::app(
                    Term::app(
                        Term::ind_id(
                            Term::nat(),
                            Term::lam(Term::lam(Term::lam(Term::u(0)))),
                            Term::lam(Term::nat()),
                        ),
                        Term::zero(),
                    ),
                    Term::zero(),
                ),
                Term::refl(Term::zero()),
            ),
            Term::nat(),
        ),
    ];
    for (term, expected) in cases {
        check(&Context::new(), &term, &Term::u(0)).unwrap();
        assert_eq!(normalize(&term), expected);
    }
    let empty = Term::ind_empty(Term::lam(Term::u(0)));
    check(
        &Context::new(),
        &empty,
        &Term::pi(Term::empty(), Term::u(0)),
    )
    .unwrap();
}

#[test]
fn motive_inference_validates_domains_universes_and_branches() {
    for family in [
        Term::typed_lam(Term::unit(), Term::u(0)), // Wrong domain.
        Term::lam(Term::zero()),                   // A value, not a type.
        Term::lam(Term::u(1)),                     // Nat : U0 cannot serve as its U1 base case.
    ] {
        let eliminator = Term::ind_nat(family, Term::nat(), Term::lam(Term::lam(Term::var(0))));
        assert!(infer(&Context::new(), &eliminator).is_err());
    }
    // A neutral motive is permitted; it need not normalize to a lambda.
    let mut context = Context::new();
    context.assume(Term::pi(Term::nat(), Term::u(1))).unwrap();
    context
        .assume(Term::app(Term::var(0), Term::zero()))
        .unwrap();
    context
        .assume(Term::pi(
            Term::nat(),
            Term::pi(
                Term::app(Term::var(2), Term::var(0)),
                Term::app(Term::var(3), Term::succ(Term::var(1))),
            ),
        ))
        .unwrap();
    let eliminator = Term::ind_nat(Term::var(2), Term::var(1), Term::var(0));
    let ty = infer(&context, &eliminator).unwrap();
    check(&context, &eliminator, &ty).unwrap();
}
