//! A small bidirectional dependent type checker.
//!
//! Bound variables use de Bruijn indices: `Var(0)` is the nearest binder.
//! The universe hierarchy is predicative and non-cumulative (`U(i) : U(i + 1)`).
//! Conversion includes beta reduction and eliminator computation, but no eta rules.
//!
//! Internal contracts and the normalization audit are in
//! `docs/kernel-invariants.md`. Raw `Term` values do not establish typing.

use super::environment::Environment;
use super::terms::*;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(usize),
    UnknownConstant(GlobalId),
    DuplicateConstant(GlobalId),
    CannotInfer(&'static str),
    ExpectedUniverse(Term),
    ExpectedFunction(Term),
    ExpectedCoproductType(Term),
    ExpectedPairType(Term),
    TypeMismatch { expected: Term, found: Term },
    DifferentIdentityTypes { left: Term, right: Term },
    ExpectedLambda(Term),
    UniverseOverflow,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownConstant(id) => write!(f, "unknown constant: {id}"),
            Self::DuplicateConstant(id) => write!(f, "duplicate constant: {id}"),
            Self::UnboundVariable(index) => {
                f.write_str("unbound variable #")?;
                fmt::Display::fmt(index, f)
            }
            Self::CannotInfer(kind) => {
                f.write_str("cannot infer a type for ")?;
                f.write_str(kind)?;
                f.write_str("; add an annotation")
            }
            Self::ExpectedUniverse(found) => {
                f.write_str("expected a type, found ")?;
                fmt::Debug::fmt(found, f)
            }
            Self::ExpectedFunction(found) => {
                f.write_str("expected a function type, found ")?;
                fmt::Debug::fmt(found, f)
            }
            Self::ExpectedPairType(found) => {
                f.write_str("expected a pair type, found ")?;
                fmt::Debug::fmt(found, f)
            }
            Self::ExpectedCoproductType(found) => {
                f.write_str("expected a coproduct type, found")?;
                fmt::Debug::fmt(found, f)
            }
            Self::ExpectedLambda(found) => {
                f.write_str("expected a lambda, found ")?;
                fmt::Debug::fmt(found, f)
            }
            Self::TypeMismatch { expected, found } => {
                f.write_str("type mismatch: expected ")?;
                fmt::Debug::fmt(expected, f)?;
                f.write_str(", found ")?;
                fmt::Debug::fmt(found, f)
            }
            Self::DifferentIdentityTypes { left, right } => {
                f.write_str("identity type mismatch: left ")?;
                fmt::Debug::fmt(left, f)?;
                f.write_str(", right ")?;
                fmt::Debug::fmt(right, f)
            }
            Self::UniverseOverflow => f.write_str("universe level overflow"),
        }
    }
}

impl std::error::Error for TypeError {}

/// Assumptions are stored oldest first. An entry's type is written in the
/// context that existed before that entry was added.
/// Every entry must be well formed in the global environment used by callers.
#[derive(Clone, Debug, Default)]
pub struct Context {
    entries: Vec<Term>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a well-formed type as the newest assumption.
    pub fn assume(&mut self, ty: Term) -> Result<(), TypeError> {
        self.assume_in(&Environment::new(), ty)
    }

    /// Requires the existing context to be valid in `env`; checks the new type
    /// before inserting it. Reusing the context with another env requires that
    /// its referenced declarations retain the same checked types and bodies.
    pub fn assume_in(&mut self, env: &Environment, ty: Term) -> Result<(), TypeError> {
        universe_level(env, self, &ty)?;
        self.entries.push(ty);
        Ok(())
    }

    /// Requires a valid context and a type well formed in that context and
    /// the same global environment. Callers establish this before extending.
    fn extended(&self, ty: Term) -> Self {
        let mut result = self.clone();
        result.entries.push(ty);
        result
    }

    /// Requires a context formed by checked extensions. Weakening crosses
    /// this assumption itself and every newer assumption (index + 1 binders).
    fn lookup(&self, index: usize) -> Result<Term, TypeError> {
        let offset = index
            .checked_add(1)
            .ok_or(TypeError::UnboundVariable(index))?;
        let position = self
            .entries
            .len()
            .checked_sub(offset)
            .ok_or(TypeError::UnboundVariable(index))?;
        // The assumption's type predates itself and every newer assumption.
        Ok(shift_up(&self.entries[position], offset, 0))
    }
}

/// Infer a term with no global declarations. Use `infer_in` for modules.
pub fn infer(context: &Context, term: &Term) -> Result<Term, TypeError> {
    infer_in(&Environment::new(), context, term)
}

/// Check a term with no global declarations. Use `check_in` for modules.
pub fn check(context: &Context, term: &Term, expected: &Term) -> Result<(), TypeError> {
    check_in(&Environment::new(), context, term, expected)
}

/// Normalize a well-typed term with no global declarations.
pub fn normalize(term: &Term) -> Term {
    normalize_in(&Environment::new(), term)
}

/// Compare well-typed terms without global declarations.
pub fn convertible(left: &Term, right: &Term) -> bool {
    convertible_in(&Environment::new(), left, right)
}

/// Infer a type for an eliminator, variable, universe, type former, annotation,
/// or typed lambda with an inferable body.
/// Requires a valid context in `env`; the input term is untrusted.
/// Success establishes that the input is well typed and the result is a
/// well-formed type in that same context. Declarations in `env` are checked.
/// The result can contain checked syntax that cannot synthesize independently.
/// Normalization removes motive redexes but may erase needed annotations too;
/// preserve this successful inference as evidence of type formation.
pub fn infer_in(env: &Environment, context: &Context, term: &Term) -> Result<Term, TypeError> {
    match term {
        Term::Universe(level) => Ok(Term::u(
            level.checked_add(1).ok_or(TypeError::UniverseOverflow)?,
        )),
        Term::Var(index) => context.lookup(*index),
        Term::TypedLambda(domain, body) => {
            // Validate the untrusted annotation before extending Γ. Successful
            // body inference supplies a valid codomain in Γ,x:domain.
            universe_level(env, context, domain)?;
            let codomain = infer_in(env, &context.extended((**domain).clone()), body)?;
            Ok(Term::pi((**domain).clone(), codomain))
        }
        Term::Const(id) => env
            .definition(id)
            .map(|definition| definition.ty().clone())
            .ok_or_else(|| TypeError::UnknownConstant(id.clone())),
        Term::Pi(domain, body) | Term::Sigma(domain, body) => {
            let domain_level = universe_level(env, context, domain)?;
            let body_level = universe_level(env, &context.extended((**domain).clone()), body)?;
            Ok(Term::u(domain_level.max(body_level)))
        }
        Term::IndSigma(sigma, type_family, curried) => {
            universe_level(env, context, sigma)?;
            // The successful universe check above establishes sigma is a type.
            let sigma = normalize_in(env, sigma);
            let Term::Sigma(a, sigma_body) = sigma.clone() else {
                return Err(TypeError::ExpectedPairType(sigma));
            };

            let type_family_type = Term::pi(sigma.clone(), Term::u(0));
            check_motive(env, context, type_family, &type_family_type, 1)?;

            // free over a,b
            let pair_case_type = Term::app(
                shift_up(&type_family, 2, 0),
                Term::pair(Term::var(1), Term::var(0)),
            );

            let curried_type = Term::pi(*a, Term::pi(*sigma_body, pair_case_type));
            check_inner(env, context, curried, &curried_type)?;
            Ok(Term::pi(sigma, apply_new_var(type_family)))
        }
        Term::Coproduct(l, r) => {
            let l_level = universe_level(env, context, l)?;
            let r_level = universe_level(env, context, r)?;
            Ok(Term::u(l_level.max(r_level)))
        }
        Term::IndCoproduct(coproduct, type_family, l_case, r_case) => {
            universe_level(env, context, coproduct)?;
            // The successful universe check above establishes a valid type.
            let coproduct = normalize_in(env, coproduct);
            let Term::Coproduct(l, r) = coproduct.clone() else {
                return Err(TypeError::ExpectedCoproductType(coproduct));
            };

            let type_family_type = Term::pi(coproduct.clone(), Term::u(0));
            check_motive(env, context, type_family, &type_family_type, 1)?;

            // free over a,b
            let l_case_type = Term::pi(
                *l,
                Term::app(
                    shift_up(type_family.as_ref(), 1, 0),
                    Term::inl(Term::var(0)),
                ),
            );

            let r_case_type = Term::pi(
                *r,
                Term::app(
                    shift_up(type_family.as_ref(), 1, 0),
                    Term::inr(Term::var(0)),
                ),
            );

            check_inner(env, context, l_case, &l_case_type)?;
            check_inner(env, context, r_case, &r_case_type)?;
            Ok(Term::pi(coproduct, apply_new_var(type_family.as_ref())))
        }
        Term::App(function, argument) => {
            // Successful inference establishes a well-formed function type.
            let function_type = normalize_in(env, &infer_in(env, context, function)?);
            match function_type {
                Term::Pi(domain, body) => {
                    check_inner(env, context, argument, &domain)?;
                    // Substitute only after argument : domain succeeds.
                    Ok(substitute_top(argument, &body))
                }
                _ => Err(TypeError::ExpectedFunction(function_type)),
            }
        }
        Term::Nat => Ok(Term::u(0)),
        Term::Empty | Term::Unit => Ok(Term::u(0)),
        Term::Tt => Ok(Term::unit()),
        Term::IndEmpty(type_family) => {
            // Empty and U0 are already well-formed types, so this motive
            // type is valid before checking the untrusted family.
            check_motive(
                env,
                context,
                type_family,
                &Term::pi(Term::empty(), Term::u(0)),
                1,
            )?;
            Ok(Term::pi(Term::empty(), apply_new_var(type_family)))
        }
        Term::IndUnit(type_family, case) => {
            check_motive(
                env,
                context,
                type_family,
                &Term::pi(Term::unit(), Term::u(0)),
                1,
            )?;
            // The checked motive and tt : Unit establish P(tt) is a type.
            check_inner(
                env,
                context,
                case,
                &Term::app((**type_family).clone(), Term::tt()),
            )?;
            Ok(Term::pi(Term::unit(), apply_new_var(type_family)))
        }
        Term::Zero => Ok(Term::nat()),
        Term::Succ(prev) => {
            check_inner(env, context, prev, &Term::nat())?;
            Ok(Term::nat())
        }
        Term::IndNat(type_family, zero_case, succ_case) => {
            check_motive(
                env,
                context,
                type_family,
                &Term::pi(Term::Nat, Term::u(0)),
                1,
            )?;

            let zero_case_type = Term::app(type_family.as_ref().clone(), Term::zero());

            let succ_case_type = Term::pi(
                Term::Nat,
                Term::pi(
                    apply_new_var(type_family),
                    Term::app(shift_up(type_family, 2, 0), Term::succ(Term::var(1))),
                ),
            );

            check_inner(env, context, zero_case, &zero_case_type)?;
            check_inner(env, context, succ_case, &succ_case_type)?;

            Ok(Term::pi(Term::Nat, apply_new_var(type_family)))
        }
        Term::Id(l, r) => 'outer: {
            let tl = infer_in(env, context, l);
            let tr = infer_in(env, context, r);

            let (inferred_type, uninferred_term) = match (tl, tr) {
                (Ok(tl), Ok(tr)) => {
                    // Both successful inferences establish valid endpoint types.
                    let (tl, tr) = (normalize_in(env, &tl), normalize_in(env, &tr));
                    if let Term::Universe(a) = tl
                        && let Term::Universe(b) = tr
                    {
                        break 'outer Ok(Term::u(
                            a.max(b).checked_add(1).ok_or(TypeError::UniverseOverflow)?,
                        ));
                    } else if convertible_in(env, &tl, &tr) {
                        let i = universe_level(env, context, &tl)?;
                        break 'outer Ok(Term::u(i));
                    } else {
                        break 'outer Err(TypeError::DifferentIdentityTypes {
                            left: tl,
                            right: tr,
                        });
                    }
                }
                (Ok(tl), Err(_)) => {
                    // Only the successfully inferred type is normalized.
                    (normalize_in(env, &tl), r)
                }
                (Err(_), Ok(tr)) => {
                    // Only the successfully inferred type is normalized.
                    (normalize_in(env, &tr), l)
                }
                (Err(_), Err(_)) => break 'outer Err(TypeError::CannotInfer("identity type")),
            };

            // Match only evaluates in cases where only on of the terms was inferrable
            check_inner(env, &context, uninferred_term, &inferred_type)?;
            let i = universe_level(env, context, &inferred_type)?;
            Ok(Term::u(i))
        }
        Term::Refl(a) => {
            infer_in(env, context, a)?;
            Ok(Term::id((**a).clone(), (**a).clone()))
        }
        Term::IndId(base, type_family, refl_case) => {
            universe_level(env, context, base)?;
            // P : Π(x:A). Π(y:A). Π(p:x=y). Ui. The second A is
            // weakened into Γ,x:A; x and y have indices 1 and 0.
            let motive_type = Term::pi(
                (**base).clone(),
                Term::pi(
                    shift_up(base, 1, 0),
                    Term::pi(Term::id(Term::var(1), Term::var(0)), Term::u(0)),
                ),
            );
            check_motive(env, context, type_family, &motive_type, 3)?;
            // d : Π(x:A). P(x,x,refl(x)). P has been checked above,
            // so its application is a valid expected type under this binder.
            let branch_type = Term::pi(
                (**base).clone(),
                Term::app(
                    Term::app(
                        Term::app(shift_up(type_family, 1, 0), Term::var(0)),
                        Term::var(0),
                    ),
                    Term::refl(Term::var(0)),
                ),
            );
            check_inner(env, context, refl_case, &branch_type)?;
            // Under x,y,p the indices are 2,1,0; P crosses all three binders.
            Ok(Term::pi(
                (**base).clone(),
                Term::pi(
                    shift_up(base, 1, 0),
                    Term::pi(
                        Term::id(Term::var(1), Term::var(0)),
                        Term::app(
                            Term::app(
                                Term::app(shift_up(type_family, 3, 0), Term::var(2)),
                                Term::var(1),
                            ),
                            Term::var(0),
                        ),
                    ),
                ),
            ))
        }
        Term::Ann(term, ty) => {
            universe_level(env, context, ty)?;
            check_inner(env, context, term, ty)?;
            Ok((**ty).clone())
        }
        Term::Inr(_) => Err(TypeError::CannotInfer("inr")),
        Term::Inl(_) => Err(TypeError::CannotInfer("inl")),
        Term::Lambda(_) => Err(TypeError::CannotInfer("lambda")),
        Term::Pair(_, _) => Err(TypeError::CannotInfer("pair")),
    }
}

/// Check a motive whose expected Π domains are already well formed.
/// Infer a motive's result universe using the known binder domains for lambdas.
/// `small_type` must have exactly `binders` Π binders ending in U0. Only that
/// terminal universe is replaced, and ordinary checking validates every domain.
fn check_motive(
    env: &Environment,
    context: &Context,
    motive: &Term,
    small_type: &Term,
    binders: usize,
) -> Result<(), TypeError> {
    fn motive_level(
        env: &Environment,
        context: &Context,
        motive: &Term,
        expected: &Term,
        binders: usize,
    ) -> Result<usize, TypeError> {
        if binders > 0 {
            let Term::Pi(domain, body_type) = expected else {
                unreachable!("internal motive type must have the specified Π spine")
            };
            if let Term::Lambda(body) | Term::TypedLambda(_, body) = motive {
                // The expected motive domains were formed from checked data.
                // Use those domains to infer the body; check_inner below also
                // validates any written lambda annotation against the domain.
                return motive_level(
                    env,
                    &context.extended((**domain).clone()),
                    body,
                    body_type,
                    binders - 1,
                );
            }
        }
        let ty = infer_in(env, context, motive)?;
        // Successful inference establishes this type is safe to normalize.
        let mut result = normalize_in(env, &ty);
        for _ in 0..binders {
            let Term::Pi(_, body) = result else {
                return Err(TypeError::ExpectedFunction(result));
            };
            result = *body;
        }
        let Term::Universe(level) = result else {
            return Err(TypeError::ExpectedUniverse(result));
        };
        Ok(level)
    }
    let level = motive_level(env, context, motive, small_type, binders)?;
    fn with_universe(ty: &Term, binders: usize, level: usize) -> Term {
        if binders == 0 {
            return Term::u(level);
        }
        let Term::Pi(domain, body) = ty else {
            unreachable!("internal motive type must have the specified Π spine")
        };
        Term::pi((**domain).clone(), with_universe(body, binders - 1, level))
    }
    check_inner(
        env,
        context,
        motive,
        &with_universe(small_type, binders, level),
    )
}

/// Check an untrusted term and expected type in a valid context in `env`.
/// The universe check validates the expected type before internal checking.
pub fn check_in(
    env: &Environment,
    context: &Context,
    term: &Term,
    expected: &Term,
) -> Result<(), TypeError> {
    universe_level(env, context, expected)?;
    check_inner(env, context, term, expected)
}

/// Requires a valid context and a well-formed expected type in `env`.
/// These may follow from prior checks plus formation/substitution rules;
/// they need not come from re-inferring every constructed expected type.
/// The input term remains untrusted. Success establishes term : expected.
fn check_inner(
    env: &Environment,
    context: &Context,
    term: &Term,
    expected: &Term,
) -> Result<(), TypeError> {
    // Every expected-type normalization below uses this entry precondition.
    match term {
        Term::TypedLambda(annotation, body) => {
            universe_level(env, context, annotation)?;
            let expected = normalize_in(env, expected);
            let Term::Pi(domain, codomain) = expected else {
                return Err(TypeError::ExpectedFunction(expected));
            };
            // Both domains are valid types: annotation by the universe check,
            // domain by the expected-type precondition. Respect the written
            // annotation even when the body only checks (e.g. an untyped lambda).
            if !convertible_in(env, annotation, &domain) {
                return Err(TypeError::TypeMismatch {
                    expected: *domain,
                    found: (**annotation).clone(),
                });
            }
            check_inner(env, &context.extended(*domain), body, &codomain)
        }
        Term::Lambda(body) => {
            let expected = normalize_in(env, expected);
            match expected {
                Term::Pi(domain, codomain) => {
                    check_inner(env, &context.extended(*domain), body, &codomain)
                }
                _ => Err(TypeError::ExpectedFunction(expected)),
            }
        }
        Term::Pair(first, second) => {
            let expected = normalize_in(env, expected);
            match expected {
                Term::Sigma(domain, codomain) => {
                    check_inner(env, context, first, &domain)?;
                    check_inner(env, context, second, &substitute_top(first, &codomain))
                }
                // Term::Product(left_type, right_type) => {
                //     check_inner(env, context, first, &left_type)?;
                //     check_inner(env, context, second, &right_type)
                // }
                _ => Err(TypeError::ExpectedPairType(expected)),
            }
        }
        Term::Inl(term) => {
            let expected = normalize_in(env, expected);
            let Term::Coproduct(left_type, _) = expected else {
                return Err(TypeError::ExpectedCoproductType(expected));
            };
            check_inner(env, context, term, &left_type)
        }
        Term::Inr(term) => {
            let expected = normalize_in(env, expected);
            let Term::Coproduct(_, right_type) = expected else {
                return Err(TypeError::ExpectedCoproductType(expected));
            };
            check_inner(env, context, term, &right_type)
        }
        _ => {
            let found = infer_in(env, context, term)?;
            if convertible_in(env, &found, expected) {
                Ok(())
            } else {
                Err(TypeError::TypeMismatch {
                    expected: expected.clone(),
                    found,
                })
            }
        }
    }
}

/// Requires a valid context; `ty` is untrusted. Successful inference precedes
/// normalization, and a universe result establishes that `ty` is a type.
fn universe_level(env: &Environment, context: &Context, ty: &Term) -> Result<usize, TypeError> {
    match normalize_in(env, &infer_in(env, context, ty)?) {
        Term::Universe(level) => Ok(level),
        found => Err(TypeError::ExpectedUniverse(found)),
    }
}

/// Conversion by beta reduction and eliminator computation, without eta.
/// Requires both terms to be well typed in compatible local contexts in env.
/// Checker callers provide an inferred type and an already valid expected type.
/// For identity endpoint types, both come from successful inference.
pub fn convertible_in(env: &Environment, left: &Term, right: &Term) -> bool {
    normalize_in(env, left) == normalize_in(env, right)
}

/// Normalize a well-typed term, including beneath binders.
/// The caller must establish typing in a valid local context in `env` before
/// entry. The context may be open: neutral variables are preserved. Every
/// global constant must belong to `env`. Raw ill-typed terms may diverge.
/// Recursive calls use component typing, checked declaration bodies, or
/// subject reduction of beta/eliminator steps; this function never infers.
pub fn normalize_in(env: &Environment, term: &Term) -> Term {
    match term {
        Term::Universe(_) | Term::Var(_) => term.clone(),
        Term::Const(id) => normalize_in(
            env,
            env.definition(id)
                .expect("normalization requires constants from its checked environment")
                .value(),
        ),
        Term::Pi(domain, body) => Term::pi(normalize_in(env, domain), normalize_in(env, body)),
        Term::Sigma(domain, body) => {
            Term::sigma(normalize_in(env, domain), normalize_in(env, body))
        }
        Term::IndSigma(sigma, type_family, curried) => Term::ind_sigma(
            normalize_in(env, sigma),
            normalize_in(env, type_family),
            normalize_in(env, curried),
        ),
        Term::Coproduct(left, right) => {
            Term::coproduct(normalize_in(env, left), normalize_in(env, right))
        }
        Term::IndCoproduct(coproduct, type_family, zero_case, succ_case) => Term::ind_coproduct(
            normalize_in(env, coproduct),
            normalize_in(env, type_family),
            normalize_in(env, zero_case),
            normalize_in(env, succ_case),
        ),
        Term::Lambda(body) => Term::lam(normalize_in(env, body)),
        // Typed input establishes body typing under the annotated binder;
        // erasing its domain does not change computation, just as for Ann.
        Term::TypedLambda(_, body) => Term::lam(normalize_in(env, body)),
        Term::IndEmpty(type_family) => Term::ind_empty(normalize_in(env, type_family)),
        Term::IndUnit(type_family, case) => {
            Term::ind_unit(normalize_in(env, type_family), normalize_in(env, case))
        }
        Term::Pair(first, second) => {
            Term::pair(normalize_in(env, first), normalize_in(env, second))
        }
        Term::App(function, argument) => 'outer: {
            // Application typing establishes both components are well typed.
            let function = normalize_in(env, function);
            let argument = normalize_in(env, argument);
            // J(A, P, d)(a)(a)(refl(a)) reduces to d(a). On well-typed
            // input, the proof's endpoints already agree with the arguments.
            if let Term::Refl(_) = &argument
                && let Term::App(applied, _) = &function
                && let Term::App(eliminator, left) = applied.as_ref()
                && let Term::IndId(_, _, refl_case) = eliminator.as_ref()
            {
                break 'outer normalize_in(
                    env,
                    &Term::app((**refl_case).clone(), (**left).clone()),
                );
            }
            let redux = match (function, argument) {
                (Term::Lambda(body), arg) => substitute_top(&arg, &body),
                (Term::IndSigma(_, _, curried), Term::Pair(a, b)) => {
                    Term::app(Term::app(*curried, *a), *b)
                }
                (Term::IndCoproduct(_, _, l_case, _), Term::Inl(inner)) => {
                    Term::app(*l_case, *inner)
                }
                (Term::IndCoproduct(_, _, _, r_case), Term::Inr(inner)) => {
                    Term::app(*r_case, *inner)
                }
                (Term::IndNat(_, zero_case, _), Term::Zero) => *zero_case,
                (Term::IndUnit(_, case), Term::Tt) => *case,
                (Term::IndNat(type_family, zero_case, succ_case), Term::Succ(n)) => Term::app(
                    Term::app(*succ_case.clone(), *n.clone()),
                    Term::app(Term::ind_nat(*type_family, *zero_case, *succ_case), *n),
                ),
                (function, arg) => {
                    break 'outer Term::app(function, arg);
                }
            };
            // Subject reduction for the matched computation rule justifies redux.
            normalize_in(env, &redux)
        }
        Term::Inr(pair) => Term::inr(normalize_in(env, pair)),
        Term::Inl(pair) => Term::inl(normalize_in(env, pair)),
        Term::Nat | Term::Zero | Term::Empty | Term::Unit | Term::Tt => term.clone(),
        Term::Succ(prev) => Term::succ(normalize_in(env, prev)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            normalize_in(env, type_family),
            normalize_in(env, zero_case),
            normalize_in(env, succ_case),
        ),
        Term::Id(l, r) => Term::id(normalize_in(env, l), normalize_in(env, r)),
        Term::Refl(t) => Term::refl(normalize_in(env, t)),
        Term::IndId(base, type_family, refl_case) => Term::ind_id(
            normalize_in(env, base),
            normalize_in(env, type_family),
            normalize_in(env, refl_case),
        ),
        Term::Ann(term, _) => normalize_in(env, term),
    }
}

/// Syntactic weakening: cutoff counts protected local binders. Callers use
/// cutoff 0 for an ambient term; traversal increments it only under binders.
fn shift_up(term: &Term, amount: usize, cutoff: usize) -> Term {
    shift(term, amount, cutoff, true)
}

/// Removed ambient binders must no longer occur in term. Every shifted index
/// must be at least amount. `substitute_top` establishes this by substitution.
fn shift_down(term: &Term, amount: usize, cutoff: usize) -> Term {
    shift(term, amount, cutoff, false)
}

fn shift(term: &Term, amount: usize, cutoff: usize, up: bool) -> Term {
    match term {
        Term::Var(index) if *index >= cutoff => {
            let shifted = if up {
                index.checked_add(amount)
            } else {
                index.checked_sub(amount)
            };
            Term::var(shifted.expect("invalid internal de Bruijn shift"))
        }
        Term::Var(_) | Term::Universe(_) | Term::Const(_) => term.clone(),
        Term::Pi(domain, body) => Term::pi(
            shift(domain, amount, cutoff, up),
            shift(body, amount, cutoff + 1, up),
        ),
        Term::Sigma(domain, body) => Term::sigma(
            shift(domain, amount, cutoff, up),
            shift(body, amount, cutoff + 1, up),
        ),
        Term::IndSigma(sigma, type_family, curried) => Term::ind_sigma(
            shift(sigma, amount, cutoff, up),
            shift(type_family, amount, cutoff, up),
            shift(curried, amount, cutoff, up),
        ),
        Term::Coproduct(left, right) => Term::coproduct(
            shift(left, amount, cutoff, up),
            shift(right, amount, cutoff, up),
        ),
        Term::IndCoproduct(coproduct, type_family, left_case, right_case) => Term::ind_coproduct(
            shift(coproduct, amount, cutoff, up),
            shift(type_family, amount, cutoff, up),
            shift(left_case, amount, cutoff, up),
            shift(right_case, amount, cutoff, up),
        ),
        Term::Lambda(body) => Term::lam(shift(body, amount, cutoff + 1, up)),
        Term::TypedLambda(domain, body) => Term::typed_lam(
            shift(domain, amount, cutoff, up),
            shift(body, amount, cutoff + 1, up),
        ),
        Term::IndEmpty(type_family) => Term::ind_empty(shift(type_family, amount, cutoff, up)),
        Term::IndUnit(type_family, case) => Term::ind_unit(
            shift(type_family, amount, cutoff, up),
            shift(case, amount, cutoff, up),
        ),
        Term::App(function, argument) => Term::app(
            shift(function, amount, cutoff, up),
            shift(argument, amount, cutoff, up),
        ),
        Term::Pair(first, second) => Term::pair(
            shift(first, amount, cutoff, up),
            shift(second, amount, cutoff, up),
        ),
        Term::Inl(term) => Term::inl(shift(term, amount, cutoff, up)),
        Term::Inr(term) => Term::inr(shift(term, amount, cutoff, up)),
        Term::Nat | Term::Zero | Term::Empty | Term::Unit | Term::Tt => term.clone(),
        Term::Succ(prev) => Term::succ(shift(prev, amount, cutoff, up)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            shift(type_family, amount, cutoff, up),
            shift(zero_case, amount, cutoff, up),
            shift(succ_case, amount, cutoff, up),
        ),
        Term::Id(l, r) => Term::id(shift(l, amount, cutoff, up), shift(r, amount, cutoff, up)),
        Term::Refl(t) => Term::refl(shift(t, amount, cutoff, up)),
        Term::IndId(type_family, zero_case, succ_case) => Term::ind_id(
            shift(type_family, amount, cutoff, up),
            shift(zero_case, amount, cutoff, up),
            shift(succ_case, amount, cutoff, up),
        ),
        Term::Ann(term, ty) => Term::ann(
            shift(term, amount, cutoff, up),
            shift(ty, amount, cutoff, up),
        ),
    }
}

/// Eliminate the newest binder. For typed use, body is scoped in Γ,x:A and
/// replacement has been checked at A in Γ. The result is scoped in Γ.
/// Raise before substitution; lower only after every removed occurrence has
/// been replaced. This helper also supports purely syntactic scoped terms.
fn substitute_top(replacement: &Term, body: &Term) -> Term {
    let raised = shift_up(replacement, 1, 0);
    shift_down(&substitute(body, 0, &raised, 0), 1, 0)
}

/// Build f(x) in Γ,x:A from f in Γ. Typed callers first establish f : Π(A).B.
/// Weakening crosses exactly one new binder before applying its Var(0).
fn apply_new_var(function: &Term) -> Term {
    Term::app(shift_up(&function, 1, 0), Term::var(0))
}

/// `depth` is the number of binders crossed inside term, not an eliminator's
/// argument count. Increment only for typed/untyped lambda bodies and Π/Σ codomains.
/// Eliminator fields bind nothing. Globals are closed to local substitution.
fn substitute(term: &Term, target: usize, replacement: &Term, depth: usize) -> Term {
    match term {
        Term::Var(index) if *index == target + depth => shift_up(replacement, depth, 0),
        Term::Var(_) | Term::Universe(_) | Term::Const(_) => term.clone(),
        Term::Pi(domain, body) => Term::pi(
            substitute(domain, target, replacement, depth),
            substitute(body, target, replacement, depth + 1),
        ),
        // Term::Func(domain, codomain) => Term::func(
        //     substitute(domain, target, replacement, depth),
        //     substitute(codomain, target, replacement, depth),
        // ),
        Term::Sigma(domain, body) => Term::sigma(
            substitute(domain, target, replacement, depth),
            substitute(body, target, replacement, depth + 1),
        ),
        Term::IndSigma(type_family, zero_case, succ_case) => Term::ind_sigma(
            substitute(type_family, target, replacement, depth),
            substitute(zero_case, target, replacement, depth),
            substitute(succ_case, target, replacement, depth),
        ),
        // Term::Product(left, right) => Term::product(
        //     substitute(left, target, replacement, depth),
        //     substitute(right, target, replacement, depth),
        // ),
        Term::Coproduct(left, right) => Term::coproduct(
            substitute(left, target, replacement, depth),
            substitute(right, target, replacement, depth),
        ),
        Term::IndCoproduct(coproduct, type_family, left_case, right_case) => Term::ind_coproduct(
            substitute(coproduct, target, replacement, depth),
            substitute(type_family, target, replacement, depth),
            substitute(left_case, target, replacement, depth),
            substitute(right_case, target, replacement, depth),
        ),
        Term::Lambda(body) => Term::lam(substitute(body, target, replacement, depth + 1)),
        Term::TypedLambda(domain, body) => Term::typed_lam(
            substitute(domain, target, replacement, depth),
            substitute(body, target, replacement, depth + 1),
        ),
        Term::IndEmpty(type_family) => {
            Term::ind_empty(substitute(type_family, target, replacement, depth))
        }
        Term::IndUnit(type_family, case) => Term::ind_unit(
            substitute(type_family, target, replacement, depth),
            substitute(case, target, replacement, depth),
        ),
        Term::App(function, argument) => Term::app(
            substitute(function, target, replacement, depth),
            substitute(argument, target, replacement, depth),
        ),
        Term::Pair(first, second) => Term::pair(
            substitute(first, target, replacement, depth),
            substitute(second, target, replacement, depth),
        ),
        Term::Inl(term) => Term::inl(substitute(term, target, replacement, depth)),
        Term::Inr(term) => Term::inr(substitute(term, target, replacement, depth)),

        Term::Nat | Term::Zero | Term::Empty | Term::Unit | Term::Tt => term.clone(),
        Term::Succ(prev) => Term::succ(substitute(prev, target, replacement, depth)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            substitute(type_family, target, replacement, depth),
            substitute(zero_case, target, replacement, depth),
            substitute(succ_case, target, replacement, depth),
        ),
        Term::Id(l, r) => Term::id(
            substitute(l, target, replacement, depth),
            substitute(r, target, replacement, depth),
        ),
        Term::Refl(t) => Term::refl(substitute(t, target, replacement, depth)),
        Term::IndId(type_family, zero_case, succ_case) => Term::ind_id(
            substitute(type_family, target, replacement, depth),
            substitute(zero_case, target, replacement, depth),
            substitute(succ_case, target, replacement, depth),
        ),

        Term::Ann(term, ty) => Term::ann(
            substitute(term, target, replacement, depth),
            substitute(ty, target, replacement, depth),
        ),
    }
}

#[cfg(test)]
#[path = "tests/mod.rs"]
mod tests;
