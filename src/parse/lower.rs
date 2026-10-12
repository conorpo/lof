use std::{collections::BTreeMap, rc::Rc};

use super::{Expr, ResolveError};
use crate::core::terms::{GlobalId, Term};

impl Expr {
    /// Resolve names into de Bruijn indices. An undeclared name is an error.
    pub fn lower(&self, external_names: &[&str]) -> Result<Term, ResolveError> {
        self.lower_with_globals(external_names, &BTreeMap::new())
    }

    /// Resolve globals to constants while retaining de Bruijn local variables.
    /// The caller supplies the checked environment containing these IDs.
    pub fn lower_with_globals(
        &self,
        external_names: &[&str],
        globals: &BTreeMap<String, GlobalId>,
    ) -> Result<Term, ResolveError> {
        let mut scope: Scope = globals
            .iter()
            .map(|(name, id)| (name.clone(), Binding::Global(id.clone())))
            .collect();
        scope.extend(
            external_names
                .iter()
                .enumerate()
                .map(|(level, name)| ((*name).to_owned(), Binding::Variable(level))),
        );
        self.lower_in(&mut scope, external_names.len())
    }

    fn lower_in(&self, scope: &mut Scope, depth: usize) -> Result<Term, ResolveError> {
        match self {
            Self::Universe(level) => Ok(Term::u(*level)),
            Self::Name(name) => match scope
                .iter()
                .rev()
                .find(|(candidate, _)| candidate == name)
                .map(|(_, binding)| binding.clone())
            {
                Some(Binding::Variable(level)) => Ok(Term::var(depth - level - 1)),
                Some(Binding::Global(id)) => Ok(Term::constant(id)),
                Some(Binding::Definition { value, scope }) => {
                    // Resolve in the definition's captured scope, but calculate
                    // indices at the use site's depth to avoid variable capture.
                    value.lower_in(&mut scope.as_ref().clone(), depth)
                }
                None => Err(ResolveError { name: name.clone() }),
            },
            Self::Pi { name, domain, body } => {
                let domain = domain.lower_in(scope, depth)?;
                let body = lower_under(scope, Some(name), body, depth)?;
                Ok(Term::pi(domain, body))
            }
            Self::Sigma { name, domain, body } => {
                let domain = domain.lower_in(scope, depth)?;
                let body = lower_under(scope, Some(name), body, depth)?;
                Ok(Term::sigma(domain, body))
            }
            Self::Lambda { name, body } => {
                Ok(Term::lam(lower_under(scope, Some(name), body, depth)?))
            }
            Self::TypedLambda { name, domain, body } => {
                // The name is not in scope in its own annotation. Outer names
                // in that annotation keep the ambient binder depth.
                let domain = domain.lower_in(scope, depth)?;
                let body = lower_under(scope, Some(name), body, depth)?;
                Ok(Term::typed_lam(domain, body))
            }
            Self::ConstantFamily { binders, body } => {
                // Anonymous motive arguments add binder depth without adding
                // source names. Outer variables weaken; globals stay fixed.
                let mut result = body.lower_in(scope, depth + binders)?;
                for _ in 0..*binders {
                    result = Term::lam(result);
                }
                Ok(result)
            }
            Self::Let { name, value, body } => {
                // Validate names even in unused definitions. This is a
                // nonrecursive binding: its RHS sees only earlier bindings.
                value.lower_in(scope, depth)?;
                let binding = Binding::Definition {
                    value: Rc::new(value.as_ref().clone()),
                    scope: Rc::new(scope.clone()),
                };
                scope.push((name.clone(), binding));
                let result = body.lower_in(scope, depth);
                scope.pop();
                result
            }
            Self::Arrow(domain, body) => {
                let domain = domain.lower_in(scope, depth)?;
                let body = lower_under(scope, None, body, depth)?;
                Ok(Term::pi(domain, body))
            }
            Self::Product(domain, body) => {
                let domain = domain.lower_in(scope, depth)?;
                let body = lower_under(scope, None, body, depth)?;
                Ok(Term::sigma(domain, body))
            }
            Self::Coproduct(left, right) => Ok(Term::coproduct(
                left.lower_in(scope, depth)?,
                right.lower_in(scope, depth)?,
            )),
            Self::App(function, argument) => Ok(Term::app(
                function.lower_in(scope, depth)?,
                argument.lower_in(scope, depth)?,
            )),
            Self::Pair(first, second) => Ok(Term::pair(
                first.lower_in(scope, depth)?,
                second.lower_in(scope, depth)?,
            )),
            Self::Inl(term) => Ok(Term::inl(term.lower_in(scope, depth)?)),
            Self::Inr(term) => Ok(Term::inr(term.lower_in(scope, depth)?)),
            Self::IndSigma(sigma, family, branch) => Ok(Term::ind_sigma(
                sigma.lower_in(scope, depth)?,
                family.lower_in(scope, depth)?,
                branch.lower_in(scope, depth)?,
            )),
            Self::IndCoproduct(coproduct, family, left, right) => Ok(Term::ind_coproduct(
                coproduct.lower_in(scope, depth)?,
                family.lower_in(scope, depth)?,
                left.lower_in(scope, depth)?,
                right.lower_in(scope, depth)?,
            )),
            Self::Nat => Ok(Term::nat()),
            Self::Empty => Ok(Term::empty()),
            Self::Unit => Ok(Term::unit()),
            Self::Tt => Ok(Term::tt()),
            Self::IndEmpty(type_family) => Ok(Term::ind_empty(type_family.lower_in(scope, depth)?)),
            Self::IndUnit(type_family, case) => Ok(Term::ind_unit(
                type_family.lower_in(scope, depth)?,
                case.lower_in(scope, depth)?,
            )),
            Self::Literal(value) => Ok(Term::from(*value)),
            Self::Zero => Ok(Term::zero()),
            Self::Succ(term) => Ok(Term::succ(term.lower_in(scope, depth)?)),
            Self::IndNat(family, zero, step) => Ok(Term::ind_nat(
                family.lower_in(scope, depth)?,
                zero.lower_in(scope, depth)?,
                step.lower_in(scope, depth)?,
            )),
            Self::IndId(base, family, branch) => Ok(Term::ind_id(
                base.lower_in(scope, depth)?,
                family.lower_in(scope, depth)?,
                branch.lower_in(scope, depth)?,
            )),
            Self::Id(left, right) => Ok(Term::id(
                left.lower_in(scope, depth)?,
                right.lower_in(scope, depth)?,
            )),
            Self::Refl(term) => Ok(Term::refl(term.lower_in(scope, depth)?)),
            Self::Ann(term, ty) => Ok(Term::ann(
                term.lower_in(scope, depth)?,
                ty.lower_in(scope, depth)?,
            )),
        }
    }
}

type Scope = Vec<(String, Binding)>;

#[derive(Clone)]
enum Binding {
    // Absolute binder levels stay stable when a definition is expanded deeper.
    Variable(usize),
    Global(GlobalId),
    Definition { value: Rc<Expr>, scope: Rc<Scope> },
}

fn lower_under(
    scope: &mut Scope,
    name: Option<&str>,
    body: &Expr,
    depth: usize,
) -> Result<Term, ResolveError> {
    if let Some(name) = name {
        scope.push((name.to_owned(), Binding::Variable(depth)));
    }
    let result = body.lower_in(scope, depth + 1);
    if name.is_some() {
        scope.pop();
    }
    result
}
