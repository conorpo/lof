#[cfg(test)]
const ARITHMETIC_LOF: &str = "./arithmetic.lof";

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        core::{kernel::Context, terms::Term},
        import_lof,
    };

    #[test]
    fn arithmetic_exports_are_available_as_named_rust_fields() {
        let arithmetic = import_lof!(ARITHMETIC_LOF; add, mul).unwrap();
        for (function, expected) in [(arithmetic.add.clone(), 5), (arithmetic.mul.clone(), 6)] {
            let application = Term::app(Term::app(function, Term::from(2)), Term::from(3));
            arithmetic
                .environment()
                .check(&Context::new(), &application, &Term::nat())
                .unwrap();
            assert_eq!(
                arithmetic.environment().normalize(&application),
                Term::from(expected)
            );
        }
        assert!(arithmetic.module().term("id_nat").is_err());
    }

    #[test]
    fn arithmetic_proof_file_checks_when_loaded() {
        let proofs = import_lof!("./tests.lof").unwrap();
        for name in [
            "addition_associative",
            "addition_commutative",
            "mul_right_unit",
            "factorial_four",
        ] {
            proofs.module().term(name).unwrap();
        }
    }

    #[test]
    fn arithmetic_operations_compute_at_boundaries_and_small_values() {
        let arithmetic = import_lof!(ARITHMETIC_LOF).unwrap();
        for (source, expected) in [
            ("add(#0,#3)", 3),
            ("add(#3,#0)", 3),
            ("mul(#0,#3)", 0),
            ("mul(#3,#0)", 0),
            ("mul(#1,#3)", 3),
            ("mul(#3,#1)", 3),
            ("pred(#0)", 0),
            ("pred(#3)", 2),
            ("sub(#2,#3)", 0),
            ("sub(#5,#2)", 3),
            ("sub(#3,#0)", 3),
            ("pow(#0,#0)", 1),
            ("pow(#0,#2)", 0),
            ("pow(#2,#3)", 8),
            ("double(#3)", 6),
            ("factorial(#0)", 1),
            ("factorial(#4)", 24),
        ] {
            let term = arithmetic.module().parse(source).unwrap();
            arithmetic
                .environment()
                .check(&Context::new(), &term, &Term::nat())
                .unwrap();
            assert_eq!(
                arithmetic.environment().normalize(&term),
                Term::from(expected),
                "{source}"
            );
        }
    }
}
