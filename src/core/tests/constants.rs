use super::super::{Context, TypeError, shift_up, substitute_top};
use crate::core::{
    environment::Environment,
    terms::{GlobalId, Term},
};

#[test]
fn constants_infer_unfold_and_stay_fixed_under_local_substitution() {
    let mut env = Environment::new();
    let ty = GlobalId::new("test::T");
    env.define(ty.clone(), Term::u(0), Term::nat()).unwrap();
    let id = GlobalId::new("test::id");
    let t = Term::constant(ty);
    env.define(id.clone(), Term::pi(t.clone(), t), Term::lam(Term::var(0)))
        .unwrap();
    let constant = Term::constant(id);
    assert_eq!(shift_up(&constant, 3, 0), constant);
    assert_eq!(substitute_top(&Term::zero(), &constant), constant);
    let application = Term::app(constant, Term::zero());
    let inferred = env.infer(&Context::new(), &application).unwrap();
    assert_eq!(env.normalize(&inferred), Term::nat());
    assert_eq!(env.normalize(&application), Term::zero());
    let mut context = Context::new();
    context.assume_in(&env, inferred).unwrap();
    assert_eq!(
        env.normalize(&env.infer(&context, &Term::var(0)).unwrap()),
        Term::nat()
    );
}

#[test]
fn environment_rejects_unbound_recursive_and_replaced_declarations() {
    let mut env = Environment::new();
    let id = GlobalId::new("test::value");
    assert!(matches!(
        env.define(id.clone(), Term::nat(), Term::var(0)),
        Err(TypeError::UnboundVariable(0))
    ));
    assert!(matches!(
        env.define(id.clone(), Term::nat(), Term::constant(id.clone())),
        Err(TypeError::UnknownConstant(_))
    ));
    assert!(env.definition(&id).is_none());
    env.define(id.clone(), Term::nat(), Term::zero()).unwrap();
    assert!(matches!(
        env.define(id.clone(), Term::nat(), Term::from(1)),
        Err(TypeError::DuplicateConstant(_))
    ));
    assert_eq!(env.normalize(&Term::constant(id)), Term::zero());
}

#[test]
fn inferred_declarations_check_before_insertion_and_keep_check_only_endpoint_types() {
    let mut env = Environment::new();
    let id = GlobalId::new("test::proof");
    for invalid in [
        Term::var(0),
        Term::constant(id.clone()),
        Term::ann(Term::zero(), Term::unit()),
    ] {
        assert!(env.define_inferred(id.clone(), invalid).is_err());
        assert!(env.definition(&id).is_none());
    }
    let value = Term::ann(
        Term::inr(Term::tt()),
        Term::coproduct(Term::unit(), Term::unit()),
    );
    env.define_inferred(id.clone(), Term::refl(value)).unwrap();
    let expected = Term::id(Term::inr(Term::tt()), Term::inr(Term::tt()));
    assert_eq!(
        env.infer(&Context::new(), &Term::constant(id.clone()))
            .unwrap(),
        expected
    );
    assert!(matches!(
        env.define_inferred(id, Term::zero()),
        Err(TypeError::DuplicateConstant(_))
    ));
}
