//! Identity elimination computation, tested independently of inference.

use super::super::normalize;
use super::super::{Context, check, infer};
use crate::core::terms::Term;

fn apply_three(function: Term, first: Term, second: Term, third: Term) -> Term {
    Term::app(Term::app(Term::app(function, first), second), third)
}

fn nat_motive() -> Term {
    Term::lam(Term::lam(Term::lam(Term::nat())))
}

#[test]
fn identity_elimination_checks_a_proof_dependent_motive_and_preserves_its_type() {
    // P(x,y,p) = (p=p), d(x) = refl(refl(x)).
    let motive = Term::lam(Term::lam(Term::lam(Term::id(Term::var(0), Term::var(0)))));
    let j = Term::ind_id(
        Term::nat(),
        motive,
        Term::lam(Term::refl(Term::refl(Term::var(0)))),
    );
    let ty = infer(&Context::new(), &j).unwrap();
    // A checked lambda motive can leave beta redexes in the inferred type.
    // Normalize those before asking the bidirectional checker to synthesize it.
    assert!(infer(&Context::new(), &normalize(&ty)).is_ok());
    let application = apply_three(j, Term::zero(), Term::zero(), Term::refl(Term::zero()));
    let result_type = Term::id(Term::refl(Term::zero()), Term::refl(Term::zero()));
    check(&Context::new(), &application, &result_type).unwrap();
    let normal = normalize(&application);
    assert_eq!(normal, Term::refl(Term::refl(Term::zero())));
    check(&Context::new(), &normal, &result_type).unwrap();
}

#[test]
fn identity_elimination_weakens_an_open_base_type() {
    let mut context = Context::new();
    context.assume(Term::u(0)).unwrap(); // A : U0
    let j = Term::ind_id(Term::var(0), nat_motive(), Term::lam(Term::zero()));
    let ty = infer(&context, &j).unwrap();
    let expected = Term::pi(
        Term::var(0),
        Term::pi(
            Term::var(1),
            Term::pi(Term::id(Term::var(1), Term::var(0)), Term::nat()),
        ),
    );
    assert_eq!(normalize(&ty), expected);
    assert!(infer(&context, &normalize(&ty)).is_ok());
}

#[test]
fn identity_elimination_reduces_after_the_proof_beta_reduces() {
    // P(x,y,p) = Nat; d(x) = succ(x).
    let eliminator = Term::ind_id(
        Term::nat(),
        nat_motive(),
        Term::lam(Term::succ(Term::var(0))),
    );
    let endpoint = Term::from(7);
    let proof = Term::app(Term::lam(Term::var(0)), Term::refl(endpoint.clone()));
    let application = apply_three(eliminator, endpoint.clone(), endpoint, proof);
    assert_eq!(normalize(&application), Term::from(8));
}

#[test]
fn identity_elimination_computes_under_a_binder() {
    // P(x,y,p) = (x = x); d(x) = refl(x).
    let motive = Term::lam(Term::lam(Term::lam(Term::id(Term::var(2), Term::var(2)))));
    let eliminator = Term::ind_id(Term::nat(), motive, Term::lam(Term::refl(Term::var(0))));
    let application = Term::lam(apply_three(
        eliminator,
        Term::var(0),
        Term::var(0),
        Term::refl(Term::var(0)),
    ));
    assert_eq!(normalize(&application), Term::lam(Term::refl(Term::var(0))));
}

#[test]
fn identity_elimination_preserves_partial_applications_and_neutral_proofs() {
    let eliminator = Term::ind_id(Term::nat(), nat_motive(), Term::lam(Term::zero()));
    let partial = Term::app(eliminator, Term::var(1));
    let two_arguments = Term::app(partial.clone(), Term::var(1));
    // In the context n:Nat, p:(n=n), the proof p remains neutral.
    let neutral = Term::app(two_arguments.clone(), Term::var(0));
    for term in [partial, two_arguments, neutral] {
        assert_eq!(normalize(&term), term);
    }

    // An unrelated neutral function applied to a reflexivity proof stays stuck.
    let unrelated = apply_three(
        Term::var(0),
        Term::zero(),
        Term::zero(),
        Term::refl(Term::zero()),
    );
    assert_eq!(normalize(&unrelated), unrelated);
}
