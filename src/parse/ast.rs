#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Universe(usize),
    Name(String),
    Pi {
        name: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    Sigma {
        name: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    Lambda {
        name: String,
        body: Box<Expr>,
    },
    TypedLambda {
        name: String,
        domain: Box<Expr>,
        body: Box<Expr>,
    },
    /// Parser-generated anonymous lambdas for constant recursion motives.
    ConstantFamily {
        binders: usize,
        body: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    Arrow(Box<Expr>, Box<Expr>),
    Product(Box<Expr>, Box<Expr>),
    Coproduct(Box<Expr>, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Pair(Box<Expr>, Box<Expr>),
    Inl(Box<Expr>),
    Inr(Box<Expr>),
    IndSigma(Box<Expr>, Box<Expr>, Box<Expr>),
    IndCoproduct(Box<Expr>, Box<Expr>, Box<Expr>, Box<Expr>),
    Nat,
    Empty,
    Unit,
    Tt,
    IndEmpty(Box<Expr>),
    IndUnit(Box<Expr>, Box<Expr>),
    Literal(u8),
    Zero,
    Succ(Box<Expr>),
    IndNat(Box<Expr>, Box<Expr>, Box<Expr>),
    IndId(Box<Expr>, Box<Expr>, Box<Expr>),
    Id(Box<Expr>, Box<Expr>),
    Refl(Box<Expr>),
    Ann(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleSyntax {
    pub imports: Vec<ImportDecl>,
    pub definitions: Vec<DefinitionDecl>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportDecl {
    pub path: String,
    pub alias: String,
    pub offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionDecl {
    pub name: String,
    pub value: Expr,
    pub exported: bool,
    pub offset: usize,
}
