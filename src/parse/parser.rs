use super::lexer::{Token, TokenKind, tokenize};
use super::{DefinitionDecl, Expr, FrontendError, ImportDecl, ModuleSyntax, ParseError};
use crate::core::terms::Term;

/// Parse names without requiring them to be declared yet.
pub fn parse(source: &str) -> Result<Expr, ParseError> {
    let tokens = tokenize(source)?;
    let mut parser = Parser { tokens, index: 0 };
    parser.scope(TokenKind::End)
}

/// A module contains imports followed by semicolon-terminated definitions.
/// Unlike an expression scope, it does not need a final expression.
pub fn parse_module(source: &str) -> Result<ModuleSyntax, ParseError> {
    let mut parser = Parser {
        tokens: tokenize(source)?,
        index: 0,
    };
    let mut imports = Vec::new();
    let mut definitions = Vec::new();
    while parser.current().kind != TokenKind::End {
        let offset = parser.current().offset;
        if parser.current().kind == TokenKind::Import {
            if !definitions.is_empty() {
                return Err(parser.error("imports must precede definitions"));
            }
            parser.index += 1;
            let TokenKind::StringLiteral(path) = parser.current().kind.clone() else {
                return Err(parser.error("expected a quoted relative import path"));
            };
            parser.index += 1;
            parser.take(TokenKind::As, "'as'")?;
            let alias = if parser.current().kind == TokenKind::Nat {
                parser.index += 1;
                "Nat".to_owned()
            } else {
                parser.name()?
            };
            parser.take(TokenKind::Semicolon, "';' after import")?;
            imports.push(ImportDecl {
                path,
                alias,
                offset,
            });
        } else {
            let exported = parser.current().kind == TokenKind::Export;
            if exported {
                parser.index += 1;
            }
            parser.take(TokenKind::Let, "'let' or 'export let'")?;
            let name = parser.name()?;
            parser.take(TokenKind::Equals, "'='")?;
            let value = parser.expression()?;
            parser.take(TokenKind::Semicolon, "';' after module definition")?;
            definitions.push(DefinitionDecl {
                name,
                value,
                exported,
                offset,
            });
        }
    }
    Ok(ModuleSyntax {
        imports,
        definitions,
    })
}

/// Parse and resolve names against assumptions ordered oldest to newest.
/// `external_names` must have the same order as the corresponding `Context`.
pub fn parse_core(source: &str, external_names: &[&str]) -> Result<Term, FrontendError> {
    Ok(parse(source)?.lower(external_names)?)
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

    fn scope(&mut self, end: TokenKind) -> Result<Expr, ParseError> {
        let mut definitions = Vec::new();
        while self.current().kind == TokenKind::Let {
            self.index += 1;
            let name = self.name()?;
            self.take(TokenKind::Equals, "'='")?;
            let value = self.expression()?;
            if self.current().kind == TokenKind::Semicolon {
                self.index += 1;
            } else if !self.current().line_break_before {
                return Err(self.error("expected ';' or a line break after let binding"));
            }
            definitions.push((name, value));
        }
        if self.current().kind == end || self.current().kind == TokenKind::End {
            return Err(self.error("expected a final expression in scope"));
        }
        let mut result = self.expression()?;
        if self.current().kind == TokenKind::Semicolon {
            self.index += 1;
        }
        if self.current().kind != end {
            return Err(self.error(if end == TokenKind::RBrace {
                "expected '}' after scope's final expression"
            } else {
                "unexpected token after expression"
            }));
        }
        for (name, value) in definitions.into_iter().rev() {
            result = Expr::Let {
                name,
                value: Box::new(value),
                body: Box::new(result),
            };
        }
        Ok(result)
    }

    fn expression(&mut self) -> Result<Expr, ParseError> {
        let term = self.unannotated_expression()?;
        if self.current().kind == TokenKind::Colon {
            self.index += 1;
            Ok(Expr::Ann(Box::new(term), Box::new(self.expression()?)))
        } else {
            Ok(term)
        }
    }

    fn unannotated_expression(&mut self) -> Result<Expr, ParseError> {
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
                let body = Box::new(self.unannotated_expression()?);
                Ok(if is_pi {
                    Expr::Pi { name, domain, body }
                } else {
                    Expr::Sigma { name, domain, body }
                })
            }
            TokenKind::Lam => {
                self.index += 1;
                let (name, domain) = if self.current().kind == TokenKind::LParen {
                    self.index += 1;
                    let name = self.name()?;
                    let domain = if self.current().kind == TokenKind::Colon {
                        self.index += 1;
                        Some(Box::new(self.expression()?))
                    } else {
                        None
                    };
                    self.take(TokenKind::RParen, "')'")?;
                    (name, domain)
                } else {
                    (self.name()?, None)
                };
                self.take(TokenKind::Dot, "'.'")?;
                let body = Box::new(self.unannotated_expression()?);
                Ok(if let Some(domain) = domain {
                    Expr::TypedLambda { name, domain, body }
                } else {
                    Expr::Lambda { name, body }
                })
            }
            _ => self.arrow(),
        }
    }

    fn arrow(&mut self) -> Result<Expr, ParseError> {
        let domain = self.identity()?;
        if self.current().kind == TokenKind::Arrow {
            self.index += 1;
            let body = self.unannotated_expression()?;
            Ok(Expr::Arrow(Box::new(domain), Box::new(body)))
        } else {
            Ok(domain)
        }
    }

    fn identity(&mut self) -> Result<Expr, ParseError> {
        let left = self.coproduct()?;
        if self.current().kind == TokenKind::Equals {
            self.index += 1;
            let right = self.coproduct()?;
            if self.current().kind == TokenKind::Equals {
                return Err(self.error("parenthesize nested identity types"));
            }
            Ok(Expr::Id(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
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
            TokenKind::Not => Ok(Expr::Arrow(
                Box::new(self.postfix()?),
                Box::new(Expr::Empty),
            )),
            TokenKind::Name(mut name) => {
                while self.current().kind == TokenKind::PathSep {
                    self.index += 1;
                    name.push_str("::");
                    name.push_str(&self.name()?);
                }
                Ok(Expr::Name(name))
            }
            TokenKind::Nat if self.current().kind == TokenKind::PathSep => {
                self.index += 1;
                Ok(Expr::Name(format!("Nat::{}", self.name()?)))
            }
            TokenKind::Nat => Ok(Expr::Nat),
            TokenKind::Empty => Ok(Expr::Empty),
            TokenKind::Unit => Ok(Expr::Unit),
            TokenKind::Tt => Ok(Expr::Tt),
            TokenKind::Star => Ok(Expr::Tt),
            TokenKind::IndEmpty | TokenKind::RecEmpty => {
                let [family] = self.arguments()?;
                let family = if kind == TokenKind::RecEmpty {
                    Expr::ConstantFamily {
                        binders: 1,
                        body: Box::new(family),
                    }
                } else {
                    family
                };
                Ok(Expr::IndEmpty(Box::new(family)))
            }
            TokenKind::IndUnit | TokenKind::RecUnit => {
                let [family, case] = self.arguments()?;
                let family = if kind == TokenKind::RecUnit {
                    Expr::ConstantFamily {
                        binders: 1,
                        body: Box::new(family),
                    }
                } else {
                    family
                };
                Ok(Expr::IndUnit(Box::new(family), Box::new(case)))
            }
            TokenKind::Literal(value) => Ok(Expr::Literal(value)),
            TokenKind::ReflName(name) => Ok(Expr::Refl(Box::new(Expr::Name(name)))),
            TokenKind::Refl => {
                let [argument] = self.arguments()?;
                Ok(Expr::Refl(Box::new(argument)))
            }
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
            TokenKind::IndSigma | TokenKind::IndNat | TokenKind::IndId => {
                let [first, second, third] = self.arguments()?;
                let (first, second, third) = (Box::new(first), Box::new(second), Box::new(third));
                Ok(if kind == TokenKind::IndSigma {
                    Expr::IndSigma(first, second, third)
                } else if kind == TokenKind::IndNat {
                    Expr::IndNat(first, second, third)
                } else {
                    Expr::IndId(first, second, third)
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
            TokenKind::RecNat => {
                let [result, zero, step] = self.arguments()?;
                Ok(Expr::IndNat(
                    Box::new(Expr::ConstantFamily {
                        binders: 1,
                        body: Box::new(result),
                    }),
                    Box::new(zero),
                    Box::new(step),
                ))
            }
            TokenKind::RecId | TokenKind::RecSigma => {
                let [base, result, branch] = self.arguments()?;
                let family = Box::new(Expr::ConstantFamily {
                    binders: if kind == TokenKind::RecId { 3 } else { 1 },
                    body: Box::new(result),
                });
                Ok(if kind == TokenKind::RecId {
                    Expr::IndId(Box::new(base), family, Box::new(branch))
                } else {
                    Expr::IndSigma(Box::new(base), family, Box::new(branch))
                })
            }
            TokenKind::RecCoproduct => {
                let [base, result, left, right] = self.arguments()?;
                Ok(Expr::IndCoproduct(
                    Box::new(base),
                    Box::new(Expr::ConstantFamily {
                        binders: 1,
                        body: Box::new(result),
                    }),
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
            TokenKind::LBrace => {
                let body = self.scope(TokenKind::RBrace)?;
                self.take(TokenKind::RBrace, "'}'")?;
                Ok(body)
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
