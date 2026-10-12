//! Capture avoidance and substitution through primitive eliminators.

use super::super::{normalize, substitute_top};
use crate::core::terms::Term;

#[test]
fn substitution_avoids_capture_under_nested_binders() {
    // (λx. λy. x) z  -->  λy. z, where z remains free.
    let application = Term::app(Term::lam(Term::lam(Term::var(1))), Term::var(0));
    assert_eq!(normalize(&application), Term::lam(Term::var(1)));
}

#[test]
fn substitution_through_eliminators_preserves_branch_binders() {
    // Under an outer x binder: λy. (y, (x, z)). Substitute Nat for x;
    // y stays bound, and the surrounding z moves from index 2 to 1.
    let branch = Term::lam(Term::pair(
        Term::var(0),
        Term::pair(Term::var(1), Term::var(2)),
    ));
    let expected_branch = Term::lam(Term::pair(
        Term::var(0),
        Term::pair(Term::nat(), Term::var(1)),
    ));
    let cases = [
        (
            Term::ind_sigma(Term::var(0), Term::var(0), branch.clone()),
            Term::ind_sigma(Term::nat(), Term::nat(), expected_branch.clone()),
        ),
        (
            Term::ind_coproduct(Term::var(0), Term::var(0), branch.clone(), branch.clone()),
            Term::ind_coproduct(
                Term::nat(),
                Term::nat(),
                expected_branch.clone(),
                expected_branch.clone(),
            ),
        ),
        (
            Term::ind_nat(Term::var(0), Term::var(0), branch),
            Term::ind_nat(Term::nat(), Term::nat(), expected_branch),
        ),
    ];

    for (body, expected) in cases {
        assert_eq!(substitute_top(&Term::nat(), &body), expected);
    }
}
