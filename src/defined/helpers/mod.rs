//! Checked LOF helper libraries. Load the file needed through `import_lof!`,
//! or use an explicit relative import from another `.lof` module.

#[cfg(test)]
mod tests {
    use crate::{
        core::{kernel::Context, terms::Term},
        import_lof,
    };

    #[test]
    fn helper_proofs_state_the_expected_generic_types() {
        let proofs = import_lof!("./tests.lof").unwrap();
        for name in [
            "classical_dne",
            "sigma_choice",
            "ntype_successor",
            "quasi_inverse_shape",
            "half_adjoint_shape",
            "identity_half_adjoint",
        ] {
            proofs.module().term(name).unwrap();
        }
    }

    #[test]
    fn option_branches_map_and_bind_compute() {
        let option = import_lof!("./option.lof").unwrap();
        for (source, expected) in [
            ("get_or(Nat,#3,none(Nat))", Term::from(3)),
            ("get_or(Nat,#0,some(Nat,#2))", Term::from(2)),
            (
                "get_or(Nat,#0,map(Nat,Nat,λn.Succ(n),some(Nat,#2)))",
                Term::from(3),
            ),
            (
                "get_or(Nat,#4,map(Nat,Nat,λn.Succ(n),none(Nat)))",
                Term::from(4),
            ),
            (
                "get_or(Nat,#4,bind(Nat,Nat,λn.none(Nat),some(Nat,#2)))",
                Term::from(4),
            ),
            (
                "get_or(Nat,#0,bind(Nat,Nat,λn.some(Nat,Succ(n)),some(Nat,#2)))",
                Term::from(3),
            ),
        ] {
            let term = option.module().parse(source).unwrap();
            option
                .environment()
                .check(&Context::new(), &term, &Term::nat())
                .unwrap();
            assert_eq!(option.environment().normalize(&term), expected, "{source}");
        }
    }

    #[test]
    fn booleans_compute_on_both_constructors() {
        let booleans = import_lof!("./bool.lof").unwrap();
        for (source, expected) in [
            ("if_then_else(Nat,#2,#3,true)", Term::from(2)),
            ("if_then_else(Nat,#2,#3,false)", Term::from(3)),
            ("if_then_else(Nat,#1,#0,and(true,false))", Term::from(0)),
            ("if_then_else(Nat,#1,#0,or(false,true))", Term::from(1)),
            ("if_then_else(Nat,#1,#0,not(false))", Term::from(1)),
        ] {
            let term = booleans.module().parse(source).unwrap();
            booleans
                .environment()
                .check(&Context::new(), &term, &Term::nat())
                .unwrap();
            assert_eq!(
                booleans.environment().normalize(&term),
                expected,
                "{source}"
            );
        }
    }

    #[test]
    fn double_negation_elimination_uses_each_decision_branch() {
        let logic = import_lof!("./logic.lof"; dne_from_decision).unwrap();
        let positive = logic
            .module()
            .parse("dne_from_decision(1,inl(*),λna.na(*))")
            .unwrap();
        logic
            .environment()
            .check(&Context::new(), &positive, &Term::unit())
            .unwrap();
        assert_eq!(logic.environment().normalize(&positive), Term::tt());

        // In the negative branch nn(na) supplies the contradiction. The
        // assumption na : Unit -> Empty remains neutral, as it must.
        let mut context = Context::new();
        context
            .assume(Term::pi(Term::unit(), Term::empty()))
            .unwrap();
        let negative = Term::app(
            Term::app(
                Term::app(logic.dne_from_decision.clone(), Term::unit()),
                Term::inr(Term::var(0)),
            ),
            Term::typed_lam(
                Term::pi(Term::unit(), Term::empty()),
                Term::app(Term::var(0), Term::tt()),
            ),
        );
        logic
            .environment()
            .check(&context, &negative, &Term::unit())
            .unwrap();
        assert_eq!(
            logic.environment().normalize(&negative),
            Term::app(
                Term::ind_empty(Term::lam(Term::unit())),
                Term::app(Term::var(0), Term::tt())
            )
        );
    }

    #[test]
    fn half_adjoint_identity_has_a_computing_triangle_witness() {
        let equivalences = import_lof!("./equivalence.lof").unwrap();
        let term = equivalences.module().parse("hae_identity(Nat)").unwrap();
        equivalences
            .environment()
            .infer(&Context::new(), &term)
            .unwrap();
        let triangle = Term::lam(Term::refl(Term::refl(Term::var(0))));
        let homotopy = Term::lam(Term::refl(Term::var(0)));
        let expected = Term::pair(
            Term::lam(Term::var(0)),
            Term::pair(homotopy.clone(), Term::pair(homotopy, triangle)),
        );
        assert_eq!(equivalences.environment().normalize(&term), expected);
    }
}
