/// A declaration's identity is independent of local binders and import aliases.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalId(pub String);

impl GlobalId {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
}

impl std::fmt::Display for GlobalId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Universe(usize),
    Var(usize),
    Const(GlobalId),
    /// An annotation makes a checkable term inferable.
    Ann(Box<Term>, Box<Term>),

    Pi(Box<Term>, Box<Term>),
    // Func(Box<Term>, Box<Term>),
    Lambda(Box<Term>),
    /// A binder annotation allows inference when the body is inferable.
    /// The domain is in the ambient context; only the body binds a variable.
    TypedLambda(Box<Term>, Box<Term>),
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

    Id(Box<Term>, Box<Term>),
    Refl(Box<Term>), //varies over both A -> B -> p -> P(p)
    // T, P, a -> P(Refl(a))
    IndId(Box<Term>, Box<Term>, Box<Term>),

    Empty,
    Unit,
    Tt,
    IndEmpty(Box<Term>),
    IndUnit(Box<Term>, Box<Term>),

    // Nats
    Nat,
    Zero,
    Succ(Box<Term>),
    // For a Pi(n:Nat). P(n), a  P(0) and Pi(n:Nat). P(n) -> P(Succ(n)).
    IndNat(Box<Term>, Box<Term>, Box<Term>),
}

impl From<u8> for Term {
    fn from(value: u8) -> Self {
        (0..value).fold(Self::zero(), |previous, _| Self::succ(previous))
    }
}

impl Term {
    pub fn constant(id: GlobalId) -> Self {
        Self::Const(id)
    }

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
    pub fn typed_lam(domain: Self, body: Self) -> Self {
        Self::TypedLambda(Box::new(domain), Box::new(body))
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
    pub fn ind_coproduct(
        coproduct: Self,
        type_family: Self,
        left_case: Self,
        right_case: Self,
    ) -> Self {
        Self::IndCoproduct(
            Box::new(coproduct),
            Box::new(type_family),
            Box::new(left_case),
            Box::new(right_case),
        )
    }
    pub fn nat() -> Self {
        Self::Nat
    }
    pub fn empty() -> Self {
        Self::Empty
    }
    pub fn unit() -> Self {
        Self::Unit
    }
    pub fn tt() -> Self {
        Self::Tt
    }
    pub fn ind_empty(type_family: Self) -> Self {
        Self::IndEmpty(Box::new(type_family))
    }
    pub fn ind_unit(type_family: Self, case: Self) -> Self {
        Self::IndUnit(Box::new(type_family), Box::new(case))
    }
    pub fn zero() -> Self {
        Self::Zero
    }
    pub fn succ(term: Self) -> Self {
        Self::Succ(Box::new(term))
    }
    pub fn ind_nat(type_family: Self, zero_case: Self, succ_case: Self) -> Self {
        Self::IndNat(
            Box::new(type_family),
            Box::new(zero_case),
            Box::new(succ_case),
        )
    }

    pub fn id(a: Self, b: Self) -> Self {
        Self::Id(Box::new(a), Box::new(b))
    }
    pub fn refl(term: Self) -> Self {
        Self::Refl(Box::new(term))
    }
    pub fn ind_id(type_family: Self, p: Self, refl_case: Self) -> Self {
        Self::IndId(Box::new(type_family), Box::new(p), Box::new(refl_case))
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
