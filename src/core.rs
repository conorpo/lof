//! A small bidirectional dependent type checker.
//!
//! Bound variables use de Bruijn indices: `Var(0)` is the nearest binder.
//! The universe hierarchy is predicative and non-cumulative (`U(i) : U(i + 1)`).
//! Conversion includes beta reduction for functions and pairs, but no eta rules.

use std::{fmt,};

use crate::core::Term::Pair;



#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Universe(usize),
    Var(usize),
    /// An annotation makes a checkable term inferable.
    Ann(Box<Term>, Box<Term>),

    Pi(Box<Term>, Box<Term>),
    // Func(Box<Term>, Box<Term>),
    Lambda(Box<Term>),
    App(Box<Term>, Box<Term>),

    // Product(Box<Term>, Box<Term>),
    Sigma(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    // For a Pi(z:A*B). P(z), a  Pi(x: A). Pi(y: B). P((x,y)) .
    // IndProduct(Box<Term>, Box<Term>),
    // S, P, branch, where S is the Sigma Type, P is the type family, and branch is the curried function that takes a pair and returns a term of type P applied to that pair.
    IndSigma(Box<Term>, Box<Term>, Box<Term>),
    
    Coproduct(Box<Term>, Box<Term>),
    // For a Pi(z:A+B). P(z), a  Pi(x: A). P(inl(x)) and Pi(y: B). P(inr(y)).
    Inl(Box<Term>),
    Inr(Box<Term>),
    IndCoproduct(Box<Term>, Box<Term>, Box<Term>, Box<Term>),


    // Nats
    Nat,
    Zero,
    Succ(Box<Term>),
    // For a Pi(n:Nat). P(n), a  P(0) and Pi(n:Nat). P(n) -> P(Succ(n)).
    IndNat(Box<Term>, Box<Term>, Box<Term>)
}

impl Term {
    pub fn u(level: usize) -> Self {
        Self::Universe(level)
    }
    pub fn var(index: usize) -> Self {
        Self::Var(index)
    }
    pub fn pi(domain: Self, body: Self) -> Self {
        Self::Pi(Box::new(domain), Box::new(body))
    }
    // Yes Pi types subsume Funcion types, but useful to have these as primitive terms as they are required for type family, dependent eliom
    // pub fn func(domain: Self, body: Self) -> Self {
    //     Self::Func(Box::new(domain), Box::new(body))
    // }
    pub fn lam(body: Self) -> Self {
        Self::Lambda(Box::new(body))
    }
    pub fn app(function: Self, argument: Self) -> Self {
        Self::App(Box::new(function), Box::new(argument))
    }
    pub fn sigma(domain: Self, body: Self) -> Self {
        Self::Sigma(Box::new(domain), Box::new(body))
    }
    // pub fn product(left: Self, right: Self) -> Self {
    //     Self::Product(Box::new(left), Box::new(right))
    // }
    pub fn pair(first: Self, second: Self) -> Self {
        Self::Pair(Box::new(first), Box::new(second))
    }
    // pub fn fst(pair: Self) -> Self {
    //     Self::Fst(Box::new(pair))
    // }
    // pub fn snd(pair: Self) -> Self {
    //     Self::Snd(Box::new(pair))
    // }
    // pub fn ind_product(body: Self) -> Self {
    //     Self::IndProduct(Box::new(body))
    // }
    pub fn ind_sigma(sigma: Self, type_family: Self, curried: Self) -> Self {
        Self::IndSigma(Box::new(sigma), Box::new(type_family), Box::new(curried))
    }

    pub fn coproduct(left: Self, right: Self) -> Self {
        Self::Coproduct(Box::new(left), Box::new(right))
    }
    pub fn inl(term: Self) -> Self {
        Self::Inl(Box::new(term))
    }
    pub fn inr(term: Self) -> Self {
        Self::Inr(Box::new(term))
    }
    pub fn ind_coproduct(coproduct: Self, type_family: Self, left_case: Self, right_case: Self) -> Self {
        Self::IndCoproduct(Box::new(coproduct), Box::new(type_family), Box::new(left_case), Box::new(right_case))
    }
    pub fn nat() -> Self {
        Self::Nat
    }
    pub fn zero() -> Self {
        Self::Zero
    }
    pub fn succ(term: Self) -> Self {
        Self::Succ(Box::new(term))
    }
    /// Build a natural-number literal as repeated successors of zero.
    pub fn from_u8(value: u8) -> Self {
        (0..value).fold(Self::zero(), |previous, _| Self::succ(previous))
    }
    pub fn ind_nat(type_family: Self, zero_case: Self, succ_case: Self) -> Self {
        Self::IndNat(Box::new(type_family), Box::new(zero_case), Box::new(succ_case))
    }

    pub fn ann(term: Self, ty: Self) -> Self {
        Self::Ann(Box::new(term), Box::new(ty))
    }

    // pub fn as_ref(&self) -> &Self
    //         Term::Universe(level) => Term::Universe(*level),
    //         Term::Var(index) => Term::Var(*index),
    //         Term::Ann(term, ty) => Term::Ann(term.as_ref().clone(), ty.as_ref().clone()),
    //         Term::Pi(domain, body) => Term::Pi(domain.as_ref().clone(), body.as_ref().clone()),
    //         Term::Lambda(body) => Term::Lambda(body.as_ref().clone()),
    //         Term::App(function, argument) => Term::App(function.as_ref().clone(), argument.as_ref().clone()),
    //         Term::Sigma(domain, body) => Term::Sigma(domain.as_ref().clone(), body.as_ref().clone()),
    //         Term::Pair(first, second) => Term::Pair(first.as_ref().clone(), second.as_ref().clone()),
    //         Term::IndSigma(type_family, curried) => Term::IndSigma(type_family.as_ref().clone(), curried.as_ref().clone()),
    //         Term::Coproduct(left, right) => Term::Coproduct(left.as_ref().clone(), right.as_ref().clone()),
    //         Term::Inl(term) => Term::Inl(term.as_ref().clone()),
    //         Term::Inr(term) => Term::Inr(term.as_ref().clone()),
    //         Term::IndCoproduct(left, right, _) => Term::IndCoproduct(left.as_ref().clone(), right.as_ref().clone(), Box::new(Term::Universe(0))),
    //         Term::Nat => Term::Nat,
    //         Term::Zero => Term::Zero,
    //         Term::Succ(prev) => Term::Succ(prev.as_ref().clone()),
    //         _ => unimplemented!(),
    //     }
    // }
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(usize),
    CannotInfer(&'static str),
    ExpectedUniverse(Term),
    ExpectedFunction(Term),
    ExpectedCoproductType(Term),
    ExpectedPairType(Term),
    TypeMismatch { expected: Term, found: Term },
    ExpectedLambda(Term),
    UniverseOverflow,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
                f.write_str("expected a coproduct type, found" )?;
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
            Self::UniverseOverflow => f.write_str("universe level overflow"),
        }
    }
}

impl std::error::Error for TypeError {}

/// Assumptions are stored oldest first. An entry's type is written in the
/// context that existed before that entry was added.
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
        universe_level(self, &ty)?;
        self.entries.push(ty);
        Ok(())
    }

    fn extended(&self, ty: Term) -> Self {
        let mut result = self.clone();
        result.entries.push(ty);
        result
    }

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


/// Infer a type for an eliminator, variable, universe, type former, or annotation.
pub fn infer(context: &Context, term: &Term) -> Result<Term, TypeError> {
    match term {
        Term::Universe(level) => Ok(Term::u(
            level.checked_add(1).ok_or(TypeError::UniverseOverflow)?,
        )),
        Term::Var(index) => context.lookup(*index),
        Term::Pi(domain, body) | Term::Sigma(domain, body) => {
            let domain_level = universe_level(context, domain)?;
            let body_level = universe_level(&context.extended((**domain).clone()), body)?;
            Ok(Term::u(domain_level.max(body_level)))
        },
        Term::IndSigma(sigma,type_family, curried) => {
            universe_level(context, sigma)?;
            let sigma = normalize(sigma);
            let Term::Sigma(a, sigma_body) = sigma.clone() else {
                return Err(TypeError::ExpectedPairType(sigma));
            };

            let type_family_type = Term::pi(sigma.clone(), Term::u(0));
            check_inner(context, type_family, &type_family_type)?;
            

            // free over a,b
            let pair_case_type = Term::app(
                shift_up(&type_family, 2, 0),
                Term::pair(
                    Term::var(1), 
                    Term::var(0)
                )
            );


            let curried_type = Term::pi(*a, 
                Term::pi(*sigma_body, 
                    pair_case_type
                )
            );
            check_inner(context, curried, &curried_type)?;
            Ok(Term::pi(sigma, apply_new_var(type_family)))
        },
        Term::Coproduct(l, r) => {
            let l_level = universe_level(context, l)?;
            let r_level = universe_level(context, r)?;
            Ok(Term::u(l_level.max(r_level)))
        },
        Term::IndCoproduct(coproduct, type_family, l_case, r_case) => {
            universe_level(context, coproduct)?;
            let coproduct = normalize(coproduct);
            let Term::Coproduct(l, r) = coproduct.clone() else {
                return Err(TypeError::ExpectedCoproductType(coproduct));
            };

            let type_family_type = Term::pi(coproduct.clone(), Term::u(0));
            check_inner(context, type_family, &type_family_type)?;
            

            // free over a,b
            let l_case_type = Term::pi(
                *l,
                Term::app(
                    shift_up(type_family.as_ref(), 1, 0), 
                    Term::inl(Term::var(0))
                )
            );

            let r_case_type = Term::pi(
                *r,
                Term::app(
                    shift_up(type_family.as_ref(), 1, 0), 
                    Term::inr(Term::var(0))
                )
            );

            check_inner(context, l_case, &l_case_type)?;
            check_inner(context, r_case, &r_case_type)?;
            Ok(Term::pi(
                coproduct,
                apply_new_var(type_family.as_ref())
            ))

        }
        Term::App(function, argument) => {
            let function_type = normalize(&infer(context, function)?);
            match function_type {
                Term::Pi(domain, body) => {
                    check_inner(context, argument, &domain)?;
                    Ok(substitute_top(argument, &body))
                },
                _ => Err(TypeError::ExpectedFunction(function_type))
            }
        },
        // Term::Fst(pair) => {
        //     let pair_type = normalize(&infer(context, pair)?);
        //     let (Term::Sigma(fst, _) | Term::Product(fst, _)) = pair_type else {
        //         return Err(TypeError::ExpectedPairType(pair_type));
        //     };  
        //     Ok(*fst)
        // },
        // Term::Snd(pair) => {
        //     let pair_type = normalize(&infer(context, pair)?);
        //     match pair_type {
        //         Term::Sigma(_, body) => {
        //             Ok(substitute_top(&Term::fst((**pair).clone()), &body))
        //         },
        //         Term::Product(_, snd) => {
        //             Ok(*snd)
        //         },
        //         _ => Err(TypeError::ExpectedPairType(pair_type)),
        //     }
        // },
        Term::Nat => {
            Ok(Term::u(0))
        },
        Term::Zero => {
            Ok(Term::nat())
        },
        Term::Succ(prev) => {
            check_inner(context, prev, &Term::nat())?;
            Ok(Term::nat())
        },
        Term::IndNat(type_family, zero_case, succ_case ) => {
            check_inner(context, type_family, &Term::pi(Term::Nat, Term::u(0)))?;

            let zero_case_type = Term::app(type_family.as_ref().clone(), Term::zero());

            let succ_case_type = Term::pi(
                Term::Nat,
                Term::pi(
                    apply_new_var(type_family),
                    Term::app(
                        shift_up(type_family, 2, 0),
                        Term::succ(Term::var(1))
                    )
                )
            );

            check_inner(context, zero_case, &zero_case_type)?;
            check_inner(context, succ_case, &succ_case_type)?;

            Ok(
                Term::pi(
                    Term::Nat,
                    apply_new_var(type_family)
                )
            )
        },
        Term::Ann(term, ty) => {
            universe_level(context, ty)?;
            check_inner(context, term, ty)?;
            Ok((**ty).clone())
        },
        Term::Inr(_) => Err(TypeError::CannotInfer("inr")),
        Term::Inl(_) => Err(TypeError::CannotInfer("inl")),
        Term::Lambda(_) => Err(TypeError::CannotInfer("lambda")),
        Term::Pair(_, _) => Err(TypeError::CannotInfer("pair")),
    }
}

/// Check a term against a well-formed type.
pub fn check(context: &Context, term: &Term, expected: &Term) -> Result<(), TypeError> {
    universe_level(context, expected)?;
    check_inner(context, term, expected)
}

fn check_inner(context: &Context, term: &Term, expected: &Term) -> Result<(), TypeError> {
    match term {
        Term::Lambda(body) => {
            let expected = normalize(expected);
            match expected {
                Term::Pi(domain, codomain) => {
                    check_inner(&context.extended(*domain), body, &codomain)
                }
                _ => Err(TypeError::ExpectedFunction(expected)),
            }
        }
        Term::Pair(first, second) => {
            let expected = normalize(expected);
            match expected {
                Term::Sigma(domain, codomain) => {
                    check_inner(context, first, &domain)?;
                    check_inner(context, second, &substitute_top(first, &codomain))
                }
                // Term::Product(left_type, right_type) => {
                //     check_inner(context, first, &left_type)?;
                //     check_inner(context, second, &right_type)
                // }
                _ => Err(TypeError::ExpectedPairType(expected)),
            }
        }
        Term::Inl(term) => {
            let expected = normalize(expected);
            let Term::Coproduct(left_type, _) = expected else {
                return Err(TypeError::ExpectedCoproductType(expected))
            };
            check_inner(context, term, &left_type)
        },
        Term::Inr(term) => {
            let expected = normalize(expected);
            let Term::Coproduct(_, right_type) = expected else {
                return Err(TypeError::ExpectedCoproductType(expected))
            };
            check_inner(context, term, &right_type)
        }
        _ => {
            let found = infer(context, term)?;
            if convertible(&found, expected) {
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

fn universe_level(context: &Context, ty: &Term) -> Result<usize, TypeError> {
    match normalize(&infer(context, ty)?) {
        Term::Universe(level) => Ok(level),
        found => Err(TypeError::ExpectedUniverse(found)),
    }
}

/// Beta conversion (including pair projections), without eta conversion.
/// I.e. elimination 
pub fn convertible(left: &Term, right: &Term) -> bool {
    normalize(left) == normalize(right)
}

/// Normalize a well-typed term, including beneath binders.
pub fn normalize(term: &Term) -> Term {
    match term {
        Term::Universe(_) | Term::Var(_) => term.clone(),
        Term::Pi(domain, body) => Term::pi(normalize(domain), normalize(body)),
        // Term::Func(domain, body) => Term::func(normalize(domain), normalize(body)),
        Term::Sigma(domain, body) => Term::sigma(normalize(domain), normalize(body)),
        Term::IndSigma(type_family, zero_case, succ_case) => Term::ind_sigma(
            normalize(type_family),
            normalize(zero_case),
            normalize(succ_case)
        ),
        // Term::Product(left, right) => Term::product(normalize(left), normalize(right)),
        Term::Coproduct(left, right) => Term::coproduct(normalize(left), normalize(right)),
        Term::IndCoproduct(coproduct, type_family, zero_case, succ_case) => Term::ind_coproduct(
            normalize(coproduct),
            normalize(type_family),
            normalize(zero_case),
            normalize(succ_case)
        ),
        Term::Lambda(body) => Term::lam(normalize(body)),
        Term::Pair(first, second) => Term::pair(normalize(first), normalize(second)),
        Term::App(function, argument) => 'outer: {
            let function = normalize(function);
            let argument = normalize(argument);
            let mut redux = None;
            match (function, argument) {
                (Term::Lambda(body), arg) => {
                    redux = Some(substitute_top(&arg, &body));
                },
                (Term::IndSigma(_, _, curried),Term::Pair(a,b)) => {
                    redux = Some(Term::app(Term::app(*curried, *a),*b));
                },
                (Term::IndCoproduct(_, _, l_case, _), Term::Inl(inner)) => {
                    redux = Some(Term::app(*l_case, *inner));
                },
                (Term::IndCoproduct(_, _, _, r_case), Term::Inr(inner)) => {
                    redux = Some(Term::app(*r_case, *inner));
                },
                (Term::IndNat(_, zero_case, _), Term::Zero) => {
                    redux = Some(*zero_case);
                },
                (Term::IndNat(type_family, zero_case, succ_case), Term::Succ(n)) => {
                    redux = Some(Term::app(
                        Term::app(*succ_case.clone(), *n.clone()),
                        Term::app(Term::ind_nat(*type_family, *zero_case, *succ_case), *n)
                    ));
                },
                (function, arg) => {
                    break 'outer Term::app(function, arg);
                }
            }
            let redux = redux.unwrap();
            normalize(&redux)
        },
        // Term::Fst(pair) => match normalize(pair) {
        //     Term:on, argument),
        //     }                
        // }
        // Term::Fst(pair) => match normalize(pair) {
        //     Term::Pair(first, _) => *first,
        //     pair => Term::fst(pair),
        // },
        // Term::Snd(pair) => match normalize(pair) {
        //     Term::Pair(_, second) => *second,
        //     pair => Term::snd(pair),
        // },
        Term::Inr(pair) => Term::inr(normalize(pair)),
        Term::Inl(pair) => Term::inl(normalize(pair)),
        Term::Nat | Term::Zero => term.clone(),
        Term::Succ(prev) => Term::succ(normalize(prev)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            normalize(type_family),
            normalize(zero_case),
            normalize(succ_case)
        ),
        Term::Ann(term, _) => normalize(term),
    }
}

fn shift_up(term: &Term, amount: usize, cutoff: usize) -> Term {
    shift(term, amount, cutoff, true)
}

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
        Term::Var(_) | Term::Universe(_) => term.clone(),
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
            shift(curried, amount, cutoff, up)
        ),
        Term::Coproduct(left, right) => Term::coproduct(
            shift(left, amount, cutoff, up),
            shift(right, amount, cutoff, up),
        ),
        Term::IndCoproduct(coproduct, type_family, left_case, right_case) => Term::ind_coproduct(
            shift(coproduct, amount, cutoff, up),
            shift(type_family, amount, cutoff, up),
            shift(left_case, amount, cutoff, up),
            shift(right_case, amount, cutoff, up)
        ),
        Term::Lambda(body) => Term::lam(shift(body, amount, cutoff + 1, up)),
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
        Term::Nat | Term::Zero => term.clone(),
        Term::Succ(prev) => Term::succ(shift(prev, amount, cutoff, up)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            shift(type_family, amount, cutoff, up),
            shift(zero_case, amount, cutoff, up),
            shift(succ_case, amount, cutoff, up)
        ),
        Term::Ann(term, ty) => Term::ann(
            shift(term, amount, cutoff, up),
            shift(ty, amount, cutoff, up),
        ),
    }
}

fn substitute_top(replacement: &Term, body: &Term) -> Term {
    let raised = shift_up(replacement, 1, 0);
    shift_down(&substitute(body, 0, &raised, 0), 1, 0)
}

// takes `λx. y x` to `(λx. y x) z` where z is a new variable at the top of of the context
fn apply_new_var(function: &Term) -> Term {
    Term::app(
        shift_up(&function, 1, 0),
        Term::var(0)
    )
}

fn substitute(term: &Term, target: usize, replacement: &Term, depth: usize) -> Term {
    match term {
        Term::Var(index) if *index == target + depth => shift_up(replacement, depth, 0),
        Term::Var(_) | Term::Universe(_) => term.clone(),
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

        Term::Nat | Term::Zero => term.clone(),
        Term::Succ(prev) => Term::succ(substitute(prev, target, replacement, depth)),
        Term::IndNat(type_family, zero_case, succ_case) => Term::ind_nat(
            substitute(type_family, target, replacement, depth),
            substitute(zero_case, target, replacement, depth),
            substitute(succ_case, target, replacement, depth)
        ),
        Term::Ann(term, ty) => Term::ann(
            substitute(term, target, replacement, depth),
            substitute(ty, target, replacement, depth),
        ),
    }
}

#[cfg(test)]
#[path = "core/eliminator_tests.rs"]
mod eliminator_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn duplicate_type() -> Term {
        // Π(A : U0). Π(b : A). Σ(x : A). A
        Term::pi(
            Term::u(0),
            Term::pi(Term::var(0), Term::sigma(Term::var(1), Term::var(2))),
        )
    }

    #[test]
    fn duplicate_checks_and_its_type_is_in_u1() {
        let duplicate = Term::lam(Term::lam(Term::pair(Term::var(0), Term::var(0))));
        check(&Context::new(), &duplicate, &duplicate_type()).unwrap();
        assert_eq!(
            infer(&Context::new(), &duplicate_type()).unwrap(),
            Term::u(1)
        );
    }

    #[test]
    fn dependent_application_substitutes_its_argument() {
        let mut context = Context::new();
        context.assume(Term::u(0)).unwrap(); // A : U0
        context.assume(Term::var(0)).unwrap(); // a : A
        let identity_type = Term::pi(
            Term::u(0), 
            Term::pi(
                Term::var(0),
                Term::var(1))
        );
        let identity = Term::ann(Term::lam(Term::lam(Term::var(0))), identity_type);
        let applied = Term::app(Term::app(identity, Term::var(1)), Term::var(0));
        assert_eq!(infer(&context, &applied).unwrap(), Term::var(1));
        assert_eq!(normalize(&applied), Term::var(0));
    }

    // #[test]
    // fn pair_projections_have_dependent_types() {
    //     let mut context = Context::new();
    //     context.assume(Term::u(0)).unwrap(); // A : U0
    //     context.assume(Term::var(0)).unwrap(); // a : A
    //     // Σ(X : U0). X, inhabited by (A, a).
    //     let pair_type = Term::sigma(Term::u(0), Term::var(0));
    //     let pair = Term::ann(Term::pair(Term::var(1), Term::var(0)), pair_type);
    //     assert_eq!(
    //         infer(&context, &Term::fst(pair.clone())).unwrap(),
    //         Term::u(0)
    //     );
    //     assert!(convertible(
    //         &infer(&context, &Term::snd(pair.clone())).unwrap(),
    //         &Term::var(1)
    //     ));
    //     assert_eq!(normalize(&Term::snd(pair)), Term::var(0));
    // }

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
                Term::ind_coproduct(
                    Term::var(0), Term::var(0), branch.clone(), branch.clone(),
                ),
                Term::ind_coproduct(
                    Term::nat(), Term::nat(), expected_branch.clone(), expected_branch.clone(),
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
}
