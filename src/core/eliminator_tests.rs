//! Constructions from HoTT Book §§1.6–1.9, using the core eliminators.
//! https://homotopytypetheory.org/book/
//! These examples need neither identity types nor univalence.

use super::*;

fn nat_function_type() -> Term {
    Term::pi(Term::nat(), Term::nat())
}

fn binary_nat_function_type() -> Term {
    Term::pi(Term::nat(), nat_function_type())
}

fn double() -> Term {
    // HoTT Book (1.9.1): double(0) = 0; double(succ n) = succ(succ(double n)).
    Term::ind_nat(
        Term::lam(Term::nat()),
        Term::zero(),
        Term::lam(Term::lam(Term::succ(Term::succ(Term::var(0))))),
    )
}

fn addition() -> Term {
    // HoTT Book (1.9.2), recursing into Nat -> Nat:
    // add(0) = λm. m; add(succ n) = λm. succ(add(n)(m)).
    Term::ind_nat(
        Term::lam(nat_function_type()),
        Term::lam(Term::var(0)),
        // λn. λrecursive_function. λm. succ(recursive_function(m)).
        Term::lam(Term::lam(Term::lam(Term::succ(Term::app(
            Term::var(1),
            Term::var(0),
        ))))),
    )
}

fn multiplication() -> Term {
    // mul(0) = λm. 0; mul(succ n) = λm. add(m)(mul(n)(m)).
    Term::ind_nat(
        Term::lam(nat_function_type()),
        Term::lam(Term::zero()),
        // λn. λrecursive_function. λm. add(m)(recursive_function(m)).
        Term::lam(Term::lam(Term::lam(Term::app(
            Term::app(addition(), Term::var(0)),
            Term::app(Term::var(1), Term::var(0)),
        )))),
    )
}

fn apply_two(function: Term, first: Term, second: Term) -> Term {
    Term::app(Term::app(function, first), second)
}

fn assert_normalizes(context: &Context, term: &Term, ty: &Term, expected: &Term) {
    eprintln!("input: {term:?}\nexpected type: {ty:?}\nexpected normal form: {expected:?}");
    check(context, term, ty).expect("input must have the expected type");
    let normal = normalize(term);
    eprintln!("actual normal form: {normal:?}");
    assert_eq!(&normal, expected);
    check(context, &normal, ty).expect("normalization must preserve typing");
    assert_eq!(
        normalize(&normal),
        normal,
        "normalization must be idempotent"
    );
}

#[test]
fn u8_literals_build_successors_of_zero() {
    assert_eq!(Term::from_u8(0), Term::zero());
    assert_eq!(
        Term::from_u8(3),
        Term::succ(Term::succ(Term::succ(Term::zero()))),
    );
    check(&Context::new(), &Term::from_u8(3), &Term::nat()).unwrap();
    let mut maximum = Term::from_u8(u8::MAX);
    for _ in 0..u8::MAX {
        let Term::Succ(previous) = maximum else {
            panic!("literal has too few successors");
        };
        maximum = *previous;
    }
    assert_eq!(maximum, Term::zero());
}

#[test]
fn arithmetic_terms_have_their_function_types() {
    let context = Context::new();
    check(&context, &double(), &nat_function_type()).unwrap();
    check(&context, &addition(), &binary_nat_function_type()).unwrap();
    check(&context, &multiplication(), &binary_nat_function_type()).unwrap();
}

#[test]
fn double_computes_using_the_induction_hypothesis() {
    for value in 0..=8 {
        eprintln!("\ndouble({value}), expected {}", value * 2);
        assert_normalizes(
            &Context::new(),
            &Term::app(double(), Term::from_u8(value)),
            &Term::nat(),
            &Term::from_u8(value * 2),
        );
    }
}

#[test]
fn addition_computes_on_numerals() {
    for first in 0..=8 {
        for second in 0..=8 {
            let term = apply_two(addition(), Term::from_u8(first), Term::from_u8(second));
            assert_normalizes(
                &Context::new(),
                &term,
                &Term::nat(),
                &Term::from_u8(first + second),
            );
        }
    }
}

#[test]
fn multiplication_computes_on_numerals() {
    for first in 0..=8 {
        for second in 0..=8 {
            let term = apply_two(
                multiplication(),
                Term::from_u8(first),
                Term::from_u8(second),
            );
            assert_normalizes(
                &Context::new(),
                &term,
                &Term::nat(),
                &Term::from_u8(first * second),
            );
        }
    }
}

#[test]
fn arithmetic_computation_rules_hold_for_open_terms() {
    let mut context = Context::new();
    context.assume(Term::nat()).unwrap(); // n
    context.assume(Term::nat()).unwrap(); // m
    let n = Term::var(1);
    let m = Term::var(0);
    let equations = [
        (apply_two(addition(), Term::zero(), m.clone()), m.clone()),
        (
            apply_two(addition(), Term::succ(n.clone()), m.clone()),
            Term::succ(apply_two(addition(), n.clone(), m.clone())),
        ),
        (
            apply_two(multiplication(), Term::zero(), m.clone()),
            Term::zero(),
        ),
        (
            apply_two(multiplication(), Term::succ(n.clone()), m.clone()),
            apply_two(addition(), m.clone(), apply_two(multiplication(), n, m)),
        ),
    ];
    for (left, right) in equations {
        check(&context, &left, &Term::nat()).unwrap();
        check(&context, &right, &Term::nat()).unwrap();
        assert!(convertible(&left, &right));
    }
}

#[test]
fn natural_number_step_receives_the_predecessor() {
    let predecessor = Term::ind_nat(
        Term::lam(Term::nat()),
        Term::zero(),
        Term::lam(Term::lam(Term::var(1))),
    );
    assert_normalizes(
        &Context::new(),
        &Term::app(predecessor, Term::from_u8(4)),
        &Term::nat(),
        &Term::from_u8(3),
    );
}

#[test]
fn sigma_projections_check_with_a_dependent_family_and_compute() {
    // HoTT Book §1.6: first : S -> A; second : Πp:S. B(first(p)).
    let mut context = Context::new();
    context.assume(Term::u(0)).unwrap(); // A : U0
    context.assume(Term::pi(Term::var(0), Term::u(0))).unwrap(); // B : A -> U0
    let sigma = Term::sigma(Term::var(1), Term::app(Term::var(1), Term::var(0)));
    let first = Term::ind_sigma(
        sigma.clone(),
        Term::lam(Term::var(2)),
        Term::lam(Term::lam(Term::var(1))),
    );
    let second_body = Term::app(
        Term::var(1),
        Term::app(shift_up(&first, 1, 0), Term::var(0)),
    );
    let second = Term::ind_sigma(
        sigma.clone(),
        Term::lam(second_body.clone()),
        Term::lam(Term::lam(Term::var(0))),
    );
    check(&context, &first, &Term::pi(sigma.clone(), Term::var(2))).unwrap();
    check(&context, &second, &Term::pi(sigma, second_body)).unwrap();

    context.assume(Term::var(1)).unwrap(); // a : A
    context
        .assume(Term::app(Term::var(1), Term::var(0)))
        .unwrap(); // b : B(a)
    let pair = Term::pair(Term::var(1), Term::var(0));
    assert_normalizes(
        &context,
        &Term::app(shift_up(&first, 2, 0), pair.clone()),
        &Term::var(3),
        &Term::var(1),
    );
    assert_normalizes(
        &context,
        &Term::app(shift_up(&second, 2, 0), pair),
        &Term::app(Term::var(2), Term::var(1)),
        &Term::var(0),
    );
}

fn coproduct_swap() -> (Term, Term, Term) {
    // HoTT Book §1.7: swap : A + B -> B + A, here with A = Nat, B = Nat -> Nat.
    let source = Term::coproduct(Term::nat(), nat_function_type());
    let target = Term::coproduct(nat_function_type(), Term::nat());
    let swap = Term::ind_coproduct(
        source.clone(),
        Term::lam(target.clone()),
        Term::lam(Term::inr(Term::var(0))),
        Term::lam(Term::inl(Term::var(0))),
    );
    (swap, source, target)
}

#[test]
fn coproduct_swap_computes_both_injections() {
    let context = Context::new();
    let (swap, source, target) = coproduct_swap();
    check(&context, &swap, &Term::pi(source, target.clone())).unwrap();
    for (input, expected) in [
        (Term::inl(Term::from_u8(2)), Term::inr(Term::from_u8(2))),
        (
            Term::inr(Term::lam(Term::var(0))),
            Term::inl(Term::lam(Term::var(0))),
        ),
    ] {
        assert_normalizes(
            &context,
            &Term::app(swap.clone(), input),
            &target,
            &expected,
        );
    }
}

#[test]
fn eliminators_preserve_neutral_applications() {
    let sigma = Term::sigma(Term::nat(), Term::nat());
    let first = Term::ind_sigma(
        sigma.clone(),
        Term::lam(Term::nat()),
        Term::lam(Term::lam(Term::var(1))),
    );
    let (swap, coproduct, swapped) = coproduct_swap();
    for (function, domain, codomain) in [
        (first, sigma, Term::nat()),
        (swap, coproduct, swapped),
        (double(), Term::nat(), Term::nat()),
    ] {
        let mut context = Context::new();
        context.assume(domain).unwrap();
        let application = Term::app(function, Term::var(0));
        assert_normalizes(&context, &application, &codomain, &application);
    }
}

#[test]
fn sigma_elimination_exposes_beta_reduced_pairs_under_binders() {
    let sigma = Term::sigma(Term::nat(), Term::nat());
    let first = Term::ind_sigma(
        sigma.clone(),
        Term::lam(Term::nat()),
        Term::lam(Term::lam(Term::var(1))),
    );
    let pair_identity = Term::ann(Term::lam(Term::var(0)), Term::pi(sigma.clone(), sigma));
    let function = Term::lam(Term::app(
        first,
        Term::app(pair_identity, Term::pair(Term::var(0), Term::zero())),
    ));
    assert_normalizes(
        &Context::new(),
        &function,
        &nat_function_type(),
        &Term::lam(Term::var(0)),
    );
}

#[test]
fn natural_number_successor_reduces_over_a_neutral_predecessor() {
    let mut context = Context::new();
    context.assume(Term::nat()).unwrap();
    let input = Term::app(double(), Term::succ(Term::var(0)));
    let expected = Term::succ(Term::succ(Term::app(double(), Term::var(0))));
    assert_normalizes(&context, &input, &Term::nat(), &expected);
}
