use super::super::{Context, TypeError, check, infer, normalize, shift_up, substitute_top};
use crate::core::terms::Term;

#[test]
fn typed_lambdas_infer_dependent_results_and_compute_after_erasure() {
    // λ(A:U0). λ(x:A). refl(x)
    let function = Term::typed_lam(
        Term::u(0),
        Term::typed_lam(Term::var(0), Term::refl(Term::var(0))),
    );
    let expected = Term::pi(
        Term::u(0),
        Term::pi(Term::var(0), Term::id(Term::var(0), Term::var(0))),
    );
    assert_eq!(infer(&Context::new(), &function).unwrap(), expected);
    let normal = normalize(&function);
    assert_eq!(normal, Term::lam(Term::lam(Term::refl(Term::var(0)))));
    check(&Context::new(), &normal, &expected).unwrap();
    let application = Term::app(Term::app(function, Term::nat()), Term::from(2));
    check(
        &Context::new(),
        &application,
        &Term::id(Term::from(2), Term::from(2)),
    )
    .unwrap();
    assert_eq!(normalize(&application), Term::refl(Term::from(2)));
}

#[test]
fn checking_uses_an_expected_body_type_but_still_validates_binder_annotations() {
    // The inner untyped lambda cannot infer, but checks with an expected Π.
    let function = Term::typed_lam(Term::nat(), Term::lam(Term::var(1)));
    let expected = Term::pi(Term::nat(), Term::pi(Term::unit(), Term::nat()));
    assert!(matches!(
        infer(&Context::new(), &function),
        Err(TypeError::CannotInfer("lambda"))
    ));
    check(&Context::new(), &function, &expected).unwrap();
    let wrong = Term::typed_lam(Term::unit(), Term::lam(Term::var(1)));
    assert!(matches!(
        check(&Context::new(), &wrong, &expected),
        Err(TypeError::TypeMismatch { .. })
    ));
    let invalid = Term::typed_lam(Term::zero(), Term::var(0));
    assert!(matches!(
        infer(&Context::new(), &invalid),
        Err(TypeError::ExpectedUniverse(_))
    ));
    assert!(matches!(
        check(&Context::new(), &invalid, &expected),
        Err(TypeError::ExpectedUniverse(_))
    ));

    // Convertible annotations need not have literally identical syntax.
    let computed_domain = Term::app(Term::typed_lam(Term::u(0), Term::var(0)), Term::nat());
    let identity = Term::typed_lam(computed_domain, Term::var(0));
    check(
        &Context::new(),
        &identity,
        &Term::pi(Term::nat(), Term::nat()),
    )
    .unwrap();
}

#[test]
fn typed_lambda_domains_use_ambient_depth_while_bodies_add_one_binder() {
    let term = Term::typed_lam(Term::var(0), Term::pair(Term::var(0), Term::var(1)));
    assert_eq!(
        shift_up(&term, 1, 0),
        Term::typed_lam(Term::var(1), Term::pair(Term::var(0), Term::var(2)))
    );
    assert_eq!(
        substitute_top(&Term::nat(), &term),
        Term::typed_lam(Term::nat(), Term::pair(Term::var(0), Term::nat()))
    );

    let nested = Term::typed_lam(Term::var(0), Term::typed_lam(Term::var(1), Term::var(2)));
    assert_eq!(
        substitute_top(&Term::nat(), &nested),
        Term::typed_lam(Term::nat(), Term::typed_lam(Term::nat(), Term::nat()))
    );
}
