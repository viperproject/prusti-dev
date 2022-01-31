use prusti_specs::specifications::common;

use rustc_hir::def_id::{DefId, LocalDefId};


use std::collections::HashMap;

pub use common::{SpecType, SpecificationId, SpecIdRef};



#[derive(Debug, Clone)]
pub enum SpecificationSet {
    Procedure(ProcedureSpecification),
    Loop(LoopSpecification),
}

impl SpecificationSet {
    #[track_caller]
    pub fn expect_procedure(&self) -> &ProcedureSpecification {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn expect_mut_procedure(&mut self) -> &mut ProcedureSpecification {
        if let SpecificationSet::Procedure(spec) = self {
            return spec;
        }
        unreachable!("expected Procedure: {:?}", self);
    }

    #[track_caller]
    pub fn expect_loop(&self) -> &LoopSpecification {
        if let SpecificationSet::Loop(spec) = self {
            return spec;
        }
        unreachable!("expected Loop: {:?}", self);
    }
}

#[derive(Debug, Clone)]
pub struct Pledge {
    pub reference: Option<()>, // TODO: pledge references
    pub lhs: Option<LocalDefId>,
    pub rhs: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct ProcedureSpecification {
    pub pres: Vec<LocalDefId>,
    pub posts: Vec<LocalDefId>,
    pub pledges: Vec<Pledge>,
    pub predicate_body: Option<LocalDefId>,
    pub pure: bool,
    pub trusted: bool,
}

impl ProcedureSpecification {
    pub fn empty() -> Self {
        ProcedureSpecification {
            pres: vec![],
            posts: vec![],
            pledges: vec![],
            predicate_body: None,
            pure: false,
            trusted: false,
        }
    }
    /// Trait implementation method refinement
    /// Choosing alternative C as discussed in
    /// https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Matthias_Erdin_MA_report.pdf
    /// pp 19-23
    ///
    /// In other words, any pre-/post-condition provided by `other` will overwrite any provided by
    /// `self`.
    #[must_use]
    pub fn refine(&self, other: &Self) -> Self {
        let pres = if other.pres.is_empty() {
            self.pres.clone()
        } else {
            other.pres.clone()
        };
        let posts = if other.posts.is_empty() {
            self.posts.clone()
        } else {
            other.posts.clone()
        };
        let pledges = if other.pledges.is_empty() {
            self.pledges.clone()
        } else {
            other.pledges.clone()
        };
        let predicate_body = if other.predicate_body.is_none() {
            self.predicate_body
        } else {
            other.predicate_body
        };
        Self {
            pres,
            posts,
            pledges,
            predicate_body,
            pure: other.pure,
            trusted: other.trusted,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopSpecification {
    pub invariant: LocalDefId,
}

/// A map of specifications keyed by crate-local DefIds.
#[derive(Default)]
pub struct DefSpecificationMap {
    pub specs: HashMap<LocalDefId, SpecificationSet>,
    pub extern_specs: HashMap<DefId, LocalDefId>,
}

impl DefSpecificationMap {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get(&self, def_id: &DefId) -> Option<&SpecificationSet> {
        let id = if let Some(spec_id) = self.extern_specs.get(def_id) {
            *spec_id
        } else {
            def_id.as_local()?
        };
        self.specs.get(&id)
    }
}
