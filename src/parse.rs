//! Named surface syntax and lowering to the de Bruijn core.

use crate::core::Term;
use std::fmt;

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
    Literal(u8),
    Zero,
    Succ(Box<Expr>),
    IndNat(Box<Expr>, Box<Expr>, Box<Expr>),
    Ann(Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Byte offset in the source string.
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at byte {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolveError {
    pub name: String,
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unbound name: {}", self.name)
    }
}

impl std::error::Error for ResolveError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendError {
    Parse(ParseError),
    Resolve(ResolveError),
}

impl fmt::Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => error.fmt(f),
            Self::Resolve(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for FrontendError {}

impl From<ParseError> for FrontendError {
    fn from(error: ParseError) -> Self {
        Self::Parse(error)
    }
}

impl From<ResolveError> for FrontendError {
    fn from(error: ResolveError) -> Self {
        Self::Resolve(error)
    }
}

/// Parse names without requiring them to be declared yet.
pub fn parse(source: &str) -> Result<Expr, ParseError> {
    let tokens = tokenize(source)?;
    let mut parser = Parser { tokens, index: 0 };
    let expression = parser.expression()?;
    if !matches!(parser.current().kind, TokenKind::End) {
        return Err(parser.error("unexpected token after expression"));
    }
    Ok(expression)
}

/// Parse and resolve names against assumptions ordered oldest to newest.
/// `external_names` must have the same order as the corresponding `Context`.
pub fn parse_core(source: &str, external_names: &[&str]) -> Result<Term, FrontendError> {
    Ok(parse(source)?.lower(external_names)?)
}

impl Expr {
    /// Resolve names into de Bruijn indices. An undeclared name is an error.
    pub fn lower(&self, external_names: &[&str]) -> Result<Term, ResolveError> {
        let mut names: Vec<Option<String>> = external_names
            .iter()
            .map(|s| Some((*s).to_owned()))
            .collect();
        self.lower_in(&mut names)
    }

    fn lower_in(&self, names: &mut Vec<Option<String>>) -> Result<Term, ResolveError> {
        match self {
            Self::Universe(level) => Ok(Term::u(*level)),
            Self::Name(name) => names
                .iter()
                .rev()
                .position(|candidate| candidate.as_deref() == Some(name))
                .map(Term::var)
                .ok_or_else(|| ResolveError { name: name.clone() }),
            Self::Pi { name, domain, body } => {
                let domain = domain.lower_in(names)?;
                let body = lower_under(names, Some(name), body)?;
                Ok(Term::pi(domain, body))
            }
            Self::Sigma { name, domain, body } => {
                let domain = domain.lower_in(names)?;
                let body = lower_under(names, Some(name), body)?;
                Ok(Term::sigma(domain, body))
            }
            Self::Lambda { name, body } => Ok(Term::lam(lower_under(names, Some(name), body)?)),
            Self::Arrow(domain, body) => {
                let domain = domain.lower_in(names)?;
                let body = lower_under(names, None, body)?;
                Ok(Term::pi(domain, body))
            }
            Self::Product(domain, body) => {
                let domain = domain.lower_in(names)?;
                let body = lower_under(names, None, body)?;
                Ok(Term::sigma(domain, body))
            }
            Self::Coproduct(left, right) => Ok(Term::coproduct(
                left.lower_in(names)?,
                right.lower_in(names)?,
            )),
            Self::App(function, argument) => Ok(Term::app(
                function.lower_in(names)?,
                argument.lower_in(names)?,
            )),
            Self::Pair(first, second) => {
                Ok(Term::pair(first.lower_in(names)?, second.lower_in(names)?))
            }
            Self::Inl(term) => Ok(Term::inl(term.lower_in(names)?)),
            Self::Inr(term) => Ok(Term::inr(term.lower_in(names)?)),
            Self::IndSigma(sigma, family, branch) => Ok(Term::ind_sigma(
                sigma.lower_in(names)?,
                family.lower_in(names)?,
                branch.lower_in(names)?,
            )),
            Self::IndCoproduct(coproduct, family, left, right) => Ok(Term::ind_coproduct(
                coproduct.lower_in(names)?,
                family.lower_in(names)?,
                left.lower_in(names)?,
                right.lower_in(names)?,
            )),
            Self::Nat => Ok(Term::nat()),
            Self::Literal(value) => Ok(Term::from_u8(*value)),
            Self::Zero => Ok(Term::zero()),
            Self::Succ(term) => Ok(Term::succ(term.lower_in(names)?)),
            Self::IndNat(family, zero, step) => Ok(Term::ind_nat(
                family.lower_in(names)?,
                zero.lower_in(names)?,
                step.lower_in(names)?,
            )),
            Self::Ann(term, ty) => Ok(Term::ann(term.lower_in(names)?, ty.lower_in(names)?)),
        }
    }
}

fn lower_under(
    names: &mut Vec<Option<String>>,
    name: Option<&str>,
    body: &Expr,
) -> Result<Term, ResolveError> {
    names.push(name.map(str::to_owned));
    let result = body.lower_in(names);
    names.pop();
    result
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Pi,
    Sig,
    Lam,
    Nat,
    Literal(u8),
    Zero,
    Succ,
    Inl,
    Inr,
    IndSigma,
    IndCoproduct,
    IndNat,
    Universe(usize),
    Name(String),
    LParen,
    RParen,
    Dot,
    Colon,
    Comma,
    Arrow,
    Star,
    Plus,
    End,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    offset: usize,
}

fn tokenize(source: &str) -> Result<Vec<Token>, ParseError> {
    let mut tokens = Vec::new();
    let mut offset = 0;
    while offset < source.len() {
        let rest = &source[offset..];
        let ch = rest.chars().next().expect("nonempty rest");
        if ch.is_whitespace() {
            offset += ch.len_utf8();
            continue;
        }
        let start = offset;
        let kind = if rest.starts_with("->") {
            offset += 2;
            TokenKind::Arrow
        } else if ch.is_ascii_digit() {
            while offset < source.len() && source.as_bytes()[offset].is_ascii_digit() {
                offset += 1;
            }
            let value = source[start..offset]
                .parse::<u8>()
                .map_err(|_| ParseError {
                    offset: start,
                    message: "natural-number literal must be between 0 and 255".to_owned(),
                })?;
            TokenKind::Literal(value)
        } else if ch.is_alphabetic() || ch == '_' {
            offset += ch.len_utf8();
            while offset < source.len() {
                let next = source[offset..].chars().next().expect("nonempty rest");
                if next.is_alphanumeric() || next == '_' || next == '\'' {
                    offset += next.len_utf8();
                } else {
                    break;
                }
            }
            match &source[start..offset] {
                "Π" => TokenKind::Pi,
                "Σ" => TokenKind::Sig,
                "λ" => TokenKind::Lam,
                "Nat" => TokenKind::Nat,
                "Zero" => TokenKind::Zero,
                "Succ" => TokenKind::Succ,
                "inl" => TokenKind::Inl,
                "inr" => TokenKind::Inr,
                "ind_Σ" => TokenKind::IndSigma,
                "ind_coproduct" => TokenKind::IndCoproduct,
                "ind_nat" => TokenKind::IndNat,
                word if word.starts_with('U')
                    && word[1..].chars().all(|c| c.is_ascii_digit())
                    && word.len() > 1 =>
                {
                    let level = word[1..].parse().map_err(|_| ParseError {
                        offset: start,
                        message: "universe level is too large".to_owned(),
                    })?;
                    TokenKind::Universe(level)
                }
                word => TokenKind::Name(word.to_owned()),
            }
        } else {
            offset += ch.len_utf8();
            match ch {
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                '.' => TokenKind::Dot,
                ':' => TokenKind::Colon,
                ',' => TokenKind::Comma,
                '*' | '×' => TokenKind::Star,
                '+' => TokenKind::Plus,
                _ => {
                    return Err(ParseError {
                        offset: start,
                        message: format!("unexpected character {ch:?}"),
                    });
                }
            }
        };
        tokens.push(Token {
            kind,
            offset: start,
        });
    }
    tokens.push(Token {
        kind: TokenKind::End,
        offset: source.len(),
    });
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    index: usize,
}

impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.index]
    }

    fn error(&self, message: &str) -> ParseError {
        ParseError {
            offset: self.current().offset,
            message: message.to_owned(),
        }
    }

    fn take(&mut self, kind: TokenKind, label: &str) -> Result<(), ParseError> {
        if self.current().kind == kind {
            self.index += 1;
            Ok(())
        } else {
            Err(self.error(&format!("expected {label}")))
        }
    }

    fn name(&mut self) -> Result<String, ParseError> {
        if let TokenKind::Name(name) = &self.current().kind {
            let name = name.clone();
            self.index += 1;
            Ok(name)
        } else {
            Err(self.error("expected binder name"))
        }
    }

    fn expression(&mut self) -> Result<Expr, ParseError> {
        match self.current().kind {
            TokenKind::Pi | TokenKind::Sig => {
                let is_pi = self.current().kind == TokenKind::Pi;
                self.index += 1;
                self.take(TokenKind::LParen, "'('")?;
                let name = self.name()?;
                self.take(TokenKind::Colon, "':'")?;
                let domain = Box::new(self.expression()?);
                self.take(TokenKind::RParen, "')'")?;
                self.take(TokenKind::Dot, "'.'")?;
                let body = Box::new(self.expression()?);
                Ok(if is_pi {
                    Expr::Pi { name, domain, body }
                } else {
                    Expr::Sigma { name, domain, body }
                })
            }
            TokenKind::Lam => {
                self.index += 1;
                self.take(TokenKind::LParen, "'('")?;
                let name = self.name()?;
                self.take(TokenKind::RParen, "')'")?;
                self.take(TokenKind::Dot, "'.'")?;
                Ok(Expr::Lambda {
                    name,
                    body: Box::new(self.expression()?),
                })
            }
            _ => {
                let term = self.arrow()?;
                if self.current().kind == TokenKind::Colon {
                    self.index += 1;
                    Ok(Expr::Ann(Box::new(term), Box::new(self.expression()?)))
                } else {
                    Ok(term)
                }
            }
        }
    }

    fn arrow(&mut self) -> Result<Expr, ParseError> {
        let domain = self.coproduct()?;
        if self.current().kind == TokenKind::Arrow {
            self.index += 1;
            let body = if matches!(
                self.current().kind,
                TokenKind::Pi | TokenKind::Sig | TokenKind::Lam
            ) {
                self.expression()?
            } else {
                self.arrow()?
            };
            Ok(Expr::Arrow(Box::new(domain), Box::new(body)))
        } else {
            Ok(domain)
        }
    }

    fn coproduct(&mut self) -> Result<Expr, ParseError> {
        let left = self.product()?;
        if self.current().kind == TokenKind::Plus {
            self.index += 1;
            Ok(Expr::Coproduct(Box::new(left), Box::new(self.coproduct()?)))
        } else {
            Ok(left)
        }
    }

    fn product(&mut self) -> Result<Expr, ParseError> {
        let first = self.postfix()?;
        if self.current().kind == TokenKind::Star {
            self.index += 1;
            Ok(Expr::Product(Box::new(first), Box::new(self.product()?)))
        } else {
            Ok(first)
        }
    }

    fn postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expression = self.atom()?;
        while self.current().kind == TokenKind::LParen {
            self.index += 1;
            if self.current().kind == TokenKind::RParen {
                return Err(self.error("expected an argument"));
            }
            loop {
                expression = Expr::App(Box::new(expression), Box::new(self.expression()?));
                if self.current().kind != TokenKind::Comma {
                    break;
                }
                self.index += 1;
            }
            self.take(TokenKind::RParen, "')'")?;
        }
        Ok(expression)
    }

    fn atom(&mut self) -> Result<Expr, ParseError> {
        let kind = self.current().kind.clone();
        self.index += 1;
        match kind {
            TokenKind::Universe(level) => Ok(Expr::Universe(level)),
            TokenKind::Name(name) => Ok(Expr::Name(name)),
            TokenKind::Nat => Ok(Expr::Nat),
            TokenKind::Literal(value) => Ok(Expr::Literal(value)),
            TokenKind::Zero => Ok(Expr::Zero),
            TokenKind::Succ | TokenKind::Inl | TokenKind::Inr => {
                let [argument] = self.arguments()?;
                let argument = Box::new(argument);
                Ok(match kind {
                    TokenKind::Succ => Expr::Succ(argument),
                    TokenKind::Inl => Expr::Inl(argument),
                    _ => Expr::Inr(argument),
                })
            }
            TokenKind::IndSigma | TokenKind::IndNat => {
                let [first, second, third] = self.arguments()?;
                let (first, second, third) = (Box::new(first), Box::new(second), Box::new(third));
                Ok(if kind == TokenKind::IndSigma {
                    Expr::IndSigma(first, second, third)
                } else {
                    Expr::IndNat(first, second, third)
                })
            }
            TokenKind::IndCoproduct => {
                let [coproduct, family, left, right] = self.arguments()?;
                Ok(Expr::IndCoproduct(
                    Box::new(coproduct),
                    Box::new(family),
                    Box::new(left),
                    Box::new(right),
                ))
            }
            TokenKind::LParen => {
                let first = self.expression()?;
                if self.current().kind == TokenKind::Comma {
                    self.index += 1;
                    let second = self.expression()?;
                    self.take(TokenKind::RParen, "')'")?;
                    Ok(Expr::Pair(Box::new(first), Box::new(second)))
                } else {
                    self.take(TokenKind::RParen, "')'")?;
                    Ok(first)
                }
            }
            _ => {
                self.index -= 1;
                Err(self.error("expected a term"))
            }
        }
    }

    fn arguments<const N: usize>(&mut self) -> Result<[Expr; N], ParseError> {
        self.take(TokenKind::LParen, "'('")?;
        let mut arguments = Vec::with_capacity(N);
        for index in 0..N {
            if index > 0 {
                self.take(TokenKind::Comma, "','")?;
            }
            arguments.push(self.expression()?);
        }
        self.take(TokenKind::RParen, "')'")?;
        Ok(arguments.try_into().expect("argument count is fixed"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{Context, check, infer, normalize};

    #[test]
    fn parses_requested_syntax_with_free_name() {
        let source = "Π(A: U0). (Σ(x:A). P(x)) -> A*A";
        let expression = parse(source).unwrap();
        assert_eq!(
            expression.lower(&[]),
            Err(ResolveError {
                name: "P".to_owned()
            })
        );
        assert_eq!(
            parse_core(source, &["P"]).unwrap(),
            Term::pi(
                Term::u(0),
                Term::pi(
                    Term::sigma(Term::var(0), Term::app(Term::var(2), Term::var(0))),
                    Term::sigma(Term::var(1), Term::var(2)),
                ),
            )
        );
    }

    #[test]
    fn precedence_and_anonymous_binders_are_correct() {
        assert_eq!(
            parse_core("A*B -> C -> D", &["A", "B", "C", "D"]).unwrap(),
            Term::pi(
                Term::sigma(Term::var(3), Term::var(3)),
                Term::pi(Term::var(2), Term::var(2)),
            )
        );
        assert_eq!(
            parse_core("Π(A: U0). Π(A: U0). A", &[]).unwrap(),
            Term::pi(Term::u(0), Term::pi(Term::u(0), Term::var(0)))
        );
    }

    #[test]
    fn parsed_terms_can_be_checked() {
        let ty = parse_core("Π(A: U0). A -> A*A", &[]).unwrap();
        let duplicate = parse_core("λ(A). λ(x). (x,x)", &[]).unwrap();
        check(&Context::new(), &duplicate, &ty).unwrap();
    }

    #[test]
    fn resolves_and_checks_explicit_polymorphic_predicate() {
        let mut context = Context::new();
        // P : Π(T : U0). T -> U0
        context
            .assume(Term::pi(Term::u(0), Term::pi(Term::var(0), Term::u(0))))
            .unwrap();
        let ty = parse_core("Π(A: U0). (Σ(x:A). P(A,x)) -> A*A", &["P"]).unwrap();
        assert_eq!(infer(&context, &ty).unwrap(), Term::u(1));
    }

    #[test]
    fn rejects_bad_syntax_and_reports_offsets() {
        let error = parse("Π(A U0). A").unwrap_err();
        assert_eq!(error.offset, 5);
        assert!(parse("A ->").is_err());
        assert!(parse("P()").is_err());
        assert!(parse("A B").is_err());
    }

    #[test]
    fn accepts_unicode_type_formers_and_annotation() {
        assert_eq!(
            parse_core("Π(A: U0). A × A", &[]).unwrap(),
            Term::pi(Term::u(0), Term::sigma(Term::var(0), Term::var(1)))
        );
        assert_eq!(
            parse_core("(λ(x). x) : (A -> A)", &["A"]).unwrap(),
            Term::ann(
                Term::lam(Term::var(0)),
                Term::pi(Term::var(0), Term::var(1))
            )
        );
        assert_eq!(
            parse_core("A -> A : U0", &["A"]).unwrap(),
            Term::ann(Term::pi(Term::var(0), Term::var(1)), Term::u(0))
        );
    }

    #[test]
    fn annotations_check_and_compute() {
        let identity = parse_core("(λ(n). n) : (Nat -> Nat)", &[]).unwrap();
        let context = Context::new();
        assert_eq!(
            infer(&context, &identity).unwrap(),
            Term::pi(Term::nat(), Term::nat())
        );
        let application = Term::app(identity, Term::from_u8(3));
        check(&context, &application, &Term::nat()).unwrap();
        assert_eq!(normalize(&application), Term::from_u8(3));
    }

    #[test]
    fn parses_natural_number_constructors_and_u8_literals() {
        for (source, expected) in [
            ("Nat", Term::nat()),
            ("Zero", Term::zero()),
            ("0", Term::zero()),
            ("Succ(2)", Term::from_u8(3)),
            ("255", Term::from_u8(u8::MAX)),
        ] {
            assert_eq!(parse_core(source, &[]).unwrap(), expected);
        }
        let error = parse("256").unwrap_err();
        assert_eq!(error.offset, 0);
        assert!(error.message.contains("255"));
    }

    #[test]
    fn coproduct_precedence_and_associativity_are_correct() {
        assert_eq!(
            parse_core("Nat*Nat + Nat -> Nat + Nat", &[]).unwrap(),
            Term::pi(
                Term::coproduct(Term::sigma(Term::nat(), Term::nat()), Term::nat()),
                Term::coproduct(Term::nat(), Term::nat()),
            ),
        );
        assert_eq!(
            parse_core("Nat + Nat + Nat", &[]).unwrap(),
            Term::coproduct(Term::nat(), Term::coproduct(Term::nat(), Term::nat())),
        );
    }

    #[test]
    fn eliminator_arguments_share_the_surrounding_scope() {
        let cases = [
            (
                "ind_Σ(S,P,c)",
                &["S", "P", "c"][..],
                Term::ind_sigma(Term::var(2), Term::var(1), Term::var(0)),
            ),
            (
                "ind_coproduct(C,P,l,r)",
                &["C", "P", "l", "r"][..],
                Term::ind_coproduct(Term::var(3), Term::var(2), Term::var(1), Term::var(0)),
            ),
            (
                "ind_nat(P,z,s)",
                &["P", "z", "s"][..],
                Term::ind_nat(Term::var(2), Term::var(1), Term::var(0)),
            ),
        ];
        for (source, names, expected) in cases {
            assert_eq!(parse_core(source, names).unwrap(), expected);
        }
    }

    #[test]
    fn parsed_eliminators_type_check_and_reduce() {
        let cases = [
            ("ind_Σ(Nat*Nat, λ(p). Nat, λ(a). λ(b). a)((2,3))", 2),
            (
                "ind_coproduct(Nat+Nat, λ(p). Nat, λ(a). Succ(a), λ(b). b)(inl(2))",
                3,
            ),
            (
                "ind_coproduct(Nat+Nat, λ(p). Nat, λ(a). Succ(a), λ(b). b)(inr(2))",
                2,
            ),
            ("ind_nat(λ(n). Nat, 5, λ(n). λ(ih). Succ(Succ(ih)))(2)", 9),
        ];
        for (source, expected) in cases {
            let term = parse_core(source, &[]).unwrap();
            check(&Context::new(), &term, &Term::nat()).unwrap();
            assert_eq!(normalize(&term), Term::from_u8(expected));
        }
    }

    #[test]
    fn parses_and_computes_hott_addition() {
        let source = "ind_nat(λ(n). Nat -> Nat, λ(m). m,
            λ(n). λ(g). λ(m). Succ(g(m)))(2,3)";
        let term = parse_core(source, &[]).unwrap();
        check(&Context::new(), &term, &Term::nat()).unwrap();
        assert_eq!(normalize(&term), Term::from_u8(5));
    }

    #[test]
    fn projections_can_be_defined_as_ordinary_named_functions() {
        assert_eq!(
            parse_core("λ(fst). fst(p)", &["p"]).unwrap(),
            Term::lam(Term::app(Term::var(0), Term::var(1))),
        );
        assert_eq!(
            parse_core("snd(p)", &["snd", "p"]).unwrap(),
            Term::app(Term::var(1), Term::var(0)),
        );
    }

    #[test]
    fn rejects_wrong_constructor_arity() {
        for source in [
            "Succ()",
            "Succ(0,1)",
            "inl()",
            "inr(0,1)",
            "ind_Σ(S,P)",
            "ind_Σ(S,P,c,x)",
            "ind_coproduct(C,P,l)",
            "ind_coproduct(C,P,l,r,x)",
            "ind_nat(P,z)",
            "ind_nat(P,z,s,x)",
        ] {
            assert!(parse(source).is_err(), "unexpectedly accepted {source}");
        }
    }
}
