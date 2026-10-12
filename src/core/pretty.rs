//! Surface notation for core terms. Binder names are generated because the
//! kernel stores de Bruijn indices. Printing never checks or normalizes terms.

use super::terms::{GlobalId, Term};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

/// Display a term using names visible in a module, when available. Constants
/// without a visible name retain their full global ID. Free variables in open
/// terms use diagnostic notation `@0`, `@1`, ... (not parser syntax).
pub struct PrettyTerm<'a> {
    term: &'a Term,
    names: Option<&'a BTreeMap<String, GlobalId>>,
}

impl Term {
    pub fn display_with_names<'a>(
        &'a self,
        names: &'a BTreeMap<String, GlobalId>,
    ) -> PrettyTerm<'a> {
        PrettyTerm {
            term: self,
            names: Some(names),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyTerm {
            term: self,
            names: None,
        }
        .fmt(f)
    }
}

impl fmt::Display for PrettyTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = Printer {
            names: self.names,
            binders: Vec::new(),
            reserved: BTreeSet::new(),
            next: 0,
        };
        printer.reserve_constants(self.term);
        printer.term(f, self.term, 0)
    }
}

// Higher numbers bind more tightly. These match the surface parser; all Π/Σ
// types retain their binders, except the special case A -> Empty (negation).
const ANNOTATION: u8 = 0;
const BINDER: u8 = 1;
const IDENTITY: u8 = 2;
const SUM: u8 = 3;
const PREFIX: u8 = 4;
const APPLICATION: u8 = 5;
const ATOM: u8 = 6;

struct Printer<'a> {
    names: Option<&'a BTreeMap<String, GlobalId>>,
    binders: Vec<String>,
    reserved: BTreeSet<String>,
    next: usize,
}

impl Printer<'_> {
    fn constant_name<'a>(&'a self, id: &'a GlobalId) -> &'a str {
        self.names
            .into_iter()
            .flat_map(|names| names.iter())
            .filter(|(_, candidate)| *candidate == id)
            .map(|(name, _)| name.as_str())
            .min_by_key(|name| (name.len(), *name))
            .unwrap_or(&id.0)
    }

    fn reserve_constants(&mut self, term: &Term) {
        match term {
            Term::Const(id) => {
                self.reserved.insert(self.constant_name(id).to_owned());
            }
            Term::Pi(a, b)
            | Term::Sigma(a, b)
            | Term::TypedLambda(a, b)
            | Term::Ann(a, b)
            | Term::App(a, b)
            | Term::Pair(a, b)
            | Term::Coproduct(a, b)
            | Term::Id(a, b)
            | Term::IndUnit(a, b) => {
                self.reserve_constants(a);
                self.reserve_constants(b);
            }
            Term::Lambda(a)
            | Term::Inl(a)
            | Term::Inr(a)
            | Term::Refl(a)
            | Term::Succ(a)
            | Term::IndEmpty(a) => self.reserve_constants(a),
            Term::IndSigma(a, b, c) | Term::IndNat(a, b, c) | Term::IndId(a, b, c) => {
                self.reserve_constants(a);
                self.reserve_constants(b);
                self.reserve_constants(c);
            }
            Term::IndCoproduct(a, b, c, d) => {
                self.reserve_constants(a);
                self.reserve_constants(b);
                self.reserve_constants(c);
                self.reserve_constants(d);
            }
            Term::Universe(_)
            | Term::Var(_)
            | Term::Nat
            | Term::Zero
            | Term::Empty
            | Term::Unit
            | Term::Tt => {}
        }
    }

    fn fresh_binder(&mut self) -> String {
        const LETTERS: &[u8] = b"xyzabcdefghijklmnopqrstuvw";
        loop {
            let letter = LETTERS[self.next % LETTERS.len()] as char;
            let round = self.next / LETTERS.len();
            let name = if round == 0 {
                letter.to_string()
            } else {
                format!("{letter}{round}")
            };
            self.next += 1;
            if !self.reserved.contains(&name) {
                return name;
            }
        }
    }

    fn binder(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        symbol: &str,
        domain: Option<&Term>,
        body: &Term,
    ) -> fmt::Result {
        let name = self.fresh_binder();
        write!(f, "{symbol}")?;
        if let Some(domain) = domain {
            write!(f, "({name}:")?;
            // An annotation is outside the scope of its own binder.
            self.term(f, domain, 0)?;
            f.write_str(")")?;
        } else {
            f.write_str(&name)?;
        }
        f.write_str(". ")?;
        self.binders.push(name);
        let result = self.term(f, body, BINDER);
        self.binders.pop();
        result
    }

    fn call(&mut self, f: &mut fmt::Formatter<'_>, name: &str, args: &[&Term]) -> fmt::Result {
        write!(f, "{name}(")?;
        for (index, arg) in args.iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            self.term(f, arg, 0)?;
        }
        f.write_str(")")
    }

    fn term(&mut self, f: &mut fmt::Formatter<'_>, term: &Term, required: u8) -> fmt::Result {
        let precedence = match term {
            Term::Ann(..) => ANNOTATION,
            Term::Pi(_, body) if **body == Term::Empty => PREFIX,
            Term::Pi(..) | Term::Sigma(..) | Term::Lambda(..) | Term::TypedLambda(..) => BINDER,
            Term::Id(..) => IDENTITY,
            Term::Coproduct(..) => SUM,
            Term::App(..) => APPLICATION,
            _ => ATOM,
        };
        let parenthesize = precedence < required;
        if parenthesize {
            f.write_str("(")?;
        }
        match term {
            Term::Universe(level) => write!(f, "U{level}")?,
            Term::Var(index) => {
                if let Some(position) = self.binders.len().checked_sub(index.saturating_add(1)) {
                    f.write_str(&self.binders[position])?;
                } else {
                    write!(f, "@{}", index - self.binders.len())?;
                }
            }
            Term::Const(id) => f.write_str(self.constant_name(id))?,
            Term::Pi(domain, body) if **body == Term::Empty => {
                f.write_str("¬")?;
                self.term(f, domain, PREFIX)?;
            }
            Term::Pi(domain, body) => self.binder(f, "Π", Some(domain), body)?,
            Term::Sigma(domain, body) => self.binder(f, "Σ", Some(domain), body)?,
            Term::Lambda(body) => self.binder(f, "λ", None, body)?,
            Term::TypedLambda(domain, body) => self.binder(f, "λ", Some(domain), body)?,
            Term::App(function, argument) => {
                self.term(f, function, APPLICATION)?;
                f.write_str("(")?;
                self.term(f, argument, 0)?;
                f.write_str(")")?;
            }
            Term::Ann(value, ty) => {
                self.term(f, value, BINDER)?;
                f.write_str(" : ")?;
                self.term(f, ty, 0)?;
            }
            Term::Pair(first, second) => {
                f.write_str("(")?;
                self.term(f, first, 0)?;
                f.write_str(", ")?;
                self.term(f, second, 0)?;
                f.write_str(")")?;
            }
            Term::Coproduct(left, right) => {
                self.term(f, left, SUM + 1)?;
                f.write_str(" + ")?;
                self.term(f, right, SUM)?;
            }
            Term::Id(left, right) => {
                self.term(f, left, IDENTITY + 1)?;
                f.write_str(" = ")?;
                self.term(f, right, IDENTITY + 1)?;
            }
            Term::Nat => f.write_str("Nat")?,
            Term::Empty => f.write_str("0")?,
            Term::Unit => f.write_str("1")?,
            Term::Tt => f.write_str("*")?,
            Term::Zero | Term::Succ(_) => {
                let mut tail = term;
                let mut value = 0u16;
                while let Term::Succ(previous) = tail {
                    if value == 255 {
                        break;
                    }
                    value += 1;
                    tail = previous;
                }
                if *tail == Term::Zero {
                    write!(f, "#{value}")?;
                } else if let Term::Succ(previous) = term {
                    self.call(f, "Succ", &[previous])?;
                }
            }
            Term::Refl(value) => self.call(f, "refl", &[value])?,
            Term::Inl(value) => self.call(f, "inl", &[value])?,
            Term::Inr(value) => self.call(f, "inr", &[value])?,
            Term::IndEmpty(p) => self.call(f, "ind0", &[p])?,
            Term::IndUnit(p, case) => self.call(f, "ind1", &[p, case])?,
            Term::IndNat(p, zero, step) => self.call(f, "ind_nat", &[p, zero, step])?,
            Term::IndSigma(s, p, case) => self.call(f, "ind_Σ", &[s, p, case])?,
            Term::IndCoproduct(s, p, left, right) => {
                self.call(f, "ind_coproduct", &[s, p, left, right])?
            }
            Term::IndId(a, p, case) => self.call(f, "ind_id", &[a, p, case])?,
        }
        if parenthesize {
            f.write_str(")")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
