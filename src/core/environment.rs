//! Checked, immutable declarations used by named constants in core terms.

use std::collections::BTreeMap;

use super::kernel::{Context, TypeError, check_in, infer_in, normalize_in};
use super::terms::{GlobalId, Term};

#[derive(Clone, Debug)]
pub struct Definition {
    ty: Term,
    value: Term,
}

impl Definition {
    pub fn ty(&self) -> &Term {
        &self.ty
    }

    pub fn value(&self) -> &Term {
        &self.value
    }
}

/// Definitions can reference only declarations already checked in this
/// environment. There is no replacement or unchecked insertion operation.
#[derive(Clone, Debug, Default)]
pub struct Environment {
    definitions: BTreeMap<GlobalId, Definition>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn definition(&self, id: &GlobalId) -> Option<&Definition> {
        self.definitions.get(id)
    }

    pub fn define(&mut self, id: GlobalId, ty: Term, value: Term) -> Result<(), TypeError> {
        if self.definitions.contains_key(&id) {
            return Err(TypeError::DuplicateConstant(id));
        }
        // The empty local context ensures the declaration is closed. Checking
        // before insertion also rules out self references and forward cycles.
        check_in(self, &Context::new(), &value, &ty)?;
        self.definitions.insert(id, Definition { ty, value });
        Ok(())
    }

    pub fn infer(&self, context: &Context, term: &Term) -> Result<Term, TypeError> {
        infer_in(self, context, term)
    }

    /// Check a closed, inferable definition before inserting it. Inference
    /// already establishes type formation; normalizing that type can erase
    /// annotations needed to synthesize it again (e.g. identity endpoints
    /// that are injections). Do not re-infer the normalized type as a gate.
    pub fn define_inferred(&mut self, id: GlobalId, value: Term) -> Result<(), TypeError> {
        if self.definitions.contains_key(&id) {
            return Err(TypeError::DuplicateConstant(id));
        }
        let ty = infer_in(self, &Context::new(), &value)?;
        // Successful inference supplies both value typing and type formation.
        let ty = normalize_in(self, &ty);
        let value = match value {
            Term::Ann(value, _) => *value,
            value => value,
        };
        self.definitions.insert(id, Definition { ty, value });
        Ok(())
    }

    pub fn check(&self, context: &Context, term: &Term, ty: &Term) -> Result<(), TypeError> {
        check_in(self, context, term, ty)
    }

    /// The term must be well typed in this environment.
    pub fn normalize(&self, term: &Term) -> Term {
        normalize_in(self, term)
    }
}
