use super::ParseError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TokenKind {
    Pi,
    Sig,
    Lam,
    Nat,
    Empty,
    Unit,
    Tt,
    IndEmpty,
    IndUnit,
    RecEmpty,
    RecUnit,
    Literal(u8),
    Zero,
    Succ,
    Inl,
    Inr,
    IndSigma,
    IndCoproduct,
    IndNat,
    IndId,
    RecNat,
    RecId,
    RecSigma,
    RecCoproduct,
    Refl,
    ReflName(String),
    Let,
    Import,
    Export,
    As,
    StringLiteral(String),
    PathSep,
    Universe(usize),
    Name(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Semicolon,
    Equals,
    Dot,
    Colon,
    Comma,
    Arrow,
    Not,
    Star,
    Plus,
    End,
}

#[derive(Clone, Debug)]
pub(super) struct Token {
    pub(super) kind: TokenKind,
    pub(super) offset: usize,
    pub(super) line_break_before: bool,
}

pub(super) fn tokenize(source: &str) -> Result<Vec<Token>, ParseError> {
    let mut tokens = Vec::new();
    let mut offset = 0;
    let mut previous_end = 0;
    while offset < source.len() {
        let rest = &source[offset..];
        let ch = rest.chars().next().expect("nonempty rest");
        if ch.is_whitespace() {
            offset += ch.len_utf8();
            continue;
        }
        if rest.starts_with("//") {
            offset += rest.find('\n').unwrap_or(rest.len());
            continue;
        }
        let start = offset;
        let kind = if rest.starts_with("::") {
            offset += 2;
            TokenKind::PathSep
        } else if ch == '"' {
            offset += 1;
            let mut value = String::new();
            let mut terminated = false;
            while offset < source.len() {
                let next = source[offset..]
                    .chars()
                    .next()
                    .expect("nonempty string rest");
                offset += next.len_utf8();
                match next {
                    '"' => {
                        terminated = true;
                        break;
                    }
                    '\\' => {
                        let escaped =
                            source[offset..].chars().next().ok_or_else(|| ParseError {
                                offset: start,
                                message: "unterminated import path".to_owned(),
                            })?;
                        offset += escaped.len_utf8();
                        if escaped != '\\' && escaped != '"' {
                            return Err(ParseError {
                                offset: offset - escaped.len_utf8(),
                                message:
                                    "only escaped quotes and backslashes are supported in paths"
                                        .to_owned(),
                            });
                        }
                        value.push(escaped);
                    }
                    '\n' | '\r' => {
                        return Err(ParseError {
                            offset: start,
                            message: "import paths cannot contain line breaks".to_owned(),
                        });
                    }
                    _ => value.push(next),
                }
            }
            if !terminated {
                return Err(ParseError {
                    offset: start,
                    message: "unterminated import path".to_owned(),
                });
            }
            TokenKind::StringLiteral(value)
        } else if rest.starts_with("->") {
            offset += 2;
            TokenKind::Arrow
        } else if ch == '#' {
            offset += 1;
            let digits_start = offset;
            while offset < source.len() && source.as_bytes()[offset].is_ascii_digit() {
                offset += 1;
            }
            let value = source[digits_start..offset]
                .parse::<u8>()
                .map_err(|_| ParseError {
                    offset: start,
                    message: "expected a natural-number literal between #0 and #255".to_owned(),
                })?;
            TokenKind::Literal(value)
        } else if ch.is_ascii_digit() {
            while offset < source.len() && source.as_bytes()[offset].is_ascii_digit() {
                offset += 1;
            }
            match &source[start..offset] {
                "0" => TokenKind::Empty,
                "1" => TokenKind::Unit,
                _ => {
                    return Err(ParseError {
                        offset: start,
                        message: "natural-number literals need a '#' prefix; 0 and 1 denote types"
                            .to_owned(),
                    });
                }
            }
        } else if ch == 'λ' {
            offset += ch.len_utf8();
            TokenKind::Lam
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
                "Nat" => TokenKind::Nat,
                "Empty" => TokenKind::Empty,
                "Unit" => TokenKind::Unit,
                "tt" => TokenKind::Tt,
                "ind0" => TokenKind::IndEmpty,
                "ind1" => TokenKind::IndUnit,
                "rec0" => TokenKind::RecEmpty,
                "rec1" => TokenKind::RecUnit,
                "Zero" => TokenKind::Zero,
                "Succ" => TokenKind::Succ,
                "inl" => TokenKind::Inl,
                "inr" => TokenKind::Inr,
                "ind_Σ" => TokenKind::IndSigma,
                "ind_coproduct" => TokenKind::IndCoproduct,
                "ind_nat" => TokenKind::IndNat,
                "ind_id" => TokenKind::IndId,
                "recNat" => TokenKind::RecNat,
                "recId" => TokenKind::RecId,
                "rec_Σ" | "recSigma" => TokenKind::RecSigma,
                "recCoproduct" => TokenKind::RecCoproduct,
                "refl" => TokenKind::Refl,
                "let" => TokenKind::Let,
                "import" => TokenKind::Import,
                "export" => TokenKind::Export,
                "as" => TokenKind::As,
                word if word.starts_with("refl_") && word.len() > 5 => {
                    TokenKind::ReflName(word[5..].to_owned())
                }
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
                '{' => TokenKind::LBrace,
                '}' => TokenKind::RBrace,
                ';' => TokenKind::Semicolon,
                '=' => TokenKind::Equals,
                '.' => TokenKind::Dot,
                ':' => TokenKind::Colon,
                ',' => TokenKind::Comma,
                '*' | '×' => TokenKind::Star,
                '+' => TokenKind::Plus,
                '→' => TokenKind::Arrow,
                '¬' => TokenKind::Not,
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
            line_break_before: source[previous_end..start].contains('\n'),
        });
        previous_end = offset;
    }
    tokens.push(Token {
        kind: TokenKind::End,
        offset: source.len(),
        line_break_before: source[previous_end..].contains('\n'),
    });
    Ok(tokens)
}
