//! Formation, introduction, application, context, and conversion rules.

use super::super::{Context, TypeError, check, infer, normalize};
use crate::core::terms::Term;

#[test]
fn dependent_lambda_and_pair_introductions_check_and_form_a_type() {
    // Π(A : U0). Π(a : A). Σ(x : A). A
    let ty = Term::pi(
        Term::u(0),
        Term::pi(Term::var(0), Term::sigma(Term::var(1), Term::var(2))),
    );
    let term = Term::lam(Term::lam(Term::pair(Term::var(0), Term::var(0))));
    check(&Context::new(), &term, &ty).unwrap();
    assert_eq!(infer(&Context::new(), &ty).unwrap(), Term::u(1));
}

#[test]
fn dependent_application_substitutes_its_argument() {
    let mut context = Context::new();
    context.assume(Term::u(0)).unwrap(); // A : U0
    context.assume(Term::var(0)).unwrap(); // a : A
    let identity_type = Term::pi(Term::u(0), Term::pi(Term::var(0), Term::var(1)));
    let identity = Term::ann(Term::lam(Term::lam(Term::var(0))), identity_type);
    let applied = Term::app(Term::app(identity, Term::var(1)), Term::var(0));
    assert_eq!(infer(&context, &applied).unwrap(), Term::var(1));
    assert_eq!(normalize(&applied), Term::var(0));
}

#[test]
fn conversion_reduces_type_level_applications() {
    let mut context = Context::new();
    context.assume(Term::u(0)).unwrap(); // A : U0
    context.assume(Term::var(0)).unwrap(); // a : A
    let type_identity = Term::ann(Term::lam(Term::var(0)), Term::pi(Term::u(0), Term::u(0)));
    let expected = Term::app(type_identity, Term::var(1));
    check(&context, &Term::var(0), &expected).unwrap();
}

#[test]
fn universes_are_predicative_and_non_cumulative() {
    let context = Context::new();
    check(&context, &Term::u(0), &Term::u(1)).unwrap();
    assert!(check(&context, &Term::u(0), &Term::u(0)).is_err());
    assert!(check(&context, &Term::u(0), &Term::u(2)).is_err());
}

#[test]
fn lookup_weakens_types_when_context_grows() {
    let mut context = Context::new();
    context.assume(Term::u(0)).unwrap();
    context.assume(Term::var(0)).unwrap();
    assert_eq!(infer(&context, &Term::var(0)).unwrap(), Term::var(1));
    assert_eq!(infer(&context, &Term::var(1)).unwrap(), Term::u(0));
}

#[test]
fn rejects_bad_types_and_unannotated_introductions() {
    let context = Context::new();
    assert!(matches!(
        infer(&context, &Term::lam(Term::var(0))),
        Err(TypeError::CannotInfer(_))
    ));
    assert!(matches!(
        infer(&context, &Term::var(0)),
        Err(TypeError::UnboundVariable(0))
    ));
    assert!(check(&context, &Term::pair(Term::u(0), Term::u(0)), &Term::u(0)).is_err());
    assert!(infer(&context, &Term::pi(Term::u(0), Term::var(1))).is_err());
}
