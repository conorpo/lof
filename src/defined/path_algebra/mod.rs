#[cfg(test)]
const PATHS_LOF: &str = "./paths.lof";

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        core::{kernel::Context, terms::Term},
        import_lof,
    };

    #[test]
    fn path_algebra_exports_check_and_compute() {
        let paths = import_lof!(PATHS_LOF; ap, inv, concat, apd).unwrap();
        for term in [&paths.ap, &paths.inv, &paths.concat, &paths.apd] {
            paths.environment().infer(&Context::new(), term).unwrap();
        }
        for (source, expected) in [
            (
                "concat(Nat,#2,#2,refl(#2),#2,refl(#2))",
                Term::refl(Term::from(2)),
            ),
            ("inv(Nat,#2,#2,refl(#2))", Term::refl(Term::from(2))),
            (
                "transport(Nat,λn.n=n,#2,#2,refl(#2),refl(#2))",
                Term::refl(Term::from(2)),
            ),
            (
                "apd(Nat,λn.n=n,λn.refl(n),#2,#2,refl(#2))",
                Term::refl(Term::refl(Term::from(2))),
            ),
        ] {
            let proof = paths.module().parse(source).unwrap();
            paths.environment().infer(&Context::new(), &proof).unwrap();
            assert_eq!(paths.environment().normalize(&proof), expected, "{source}");
        }
    }

    #[test]
    fn path_algebra_proof_file_checks_when_loaded() {
        let proofs = import_lof!("./tests.lof").unwrap();
        for name in [
            "associativity",
            "dependent_action",
            "assoc_computes",
            "apd_computes",
        ] {
            proofs.module().term(name).unwrap();
        }
    }
}
