use std::collections::HashMap;
use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_mir::borrow_check::universal_regions::UniversalRegions;
use rustc_mir::borrow_check::facts::AllFacts;
use rustc_mir::borrow_check::nll::PoloniusOutput;

#[derive(PartialOrd, Ord, PartialEq, Eq)]
pub struct Lifetime {
    region: ty::RegionVid,
}

impl std::fmt::Debug for Lifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.region.index())
    }
}

impl From<ty::RegionVid> for Lifetime {
    fn from(region: ty::RegionVid) -> Self {
        Self { region }
    }
}

/// A constraint between two lifetimes: the `longer` lifetime outlives the
/// `shorter` lifetime.
///
/// Note: We cannot have “equal” constraint because the compiler gives us only
/// “outlives”. (Equal is represented as symmetric outlives constraints.)
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq)]
pub struct LifetimeConstraint {
    /// The lifetime that outlives the `shorter` lifetime.
    longer: Lifetime,
    /// The lifetime that is outlived by the `longer` lifetime.
    shorter: Lifetime,
}

impl std::fmt::Display for LifetimeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} ⊒ {:?}", self.longer, self.shorter)
    }
}

/// A location in the MIR body.
pub(super) enum Location {
    /// A statement inside the basic block.
    Statement {
        basic_block: mir::BasicBlock,
        statement: usize,
    },
    /// A terminator inside the basic block.
    Terminator {
        basic_block: mir::BasicBlock,
    },
    /// An edge between two basic blocks.
    Edge {
        start: mir::BasicBlock,
        end: mir::BasicBlock,
    },
}

pub(super) struct BodyLifetimes {
    /// Lifetimes that must be alive for the entire function.
    pub(super) universal_lifetimes: Vec<Lifetime>,
    /// Constraints between the universal lifetimes.
    pub(super) universal_lifetime_constraints: Vec<LifetimeConstraint>,
    /// The lifetimes that start at the given program point.
    pub(super) lifetimes_starting_at: HashMap<Location, Vec<Lifetime>>,
    /// The lifetimes that end at the given program point.
    pub(super) lifetimes_ending_at: HashMap<Location, Vec<Lifetime>>,
    /// The lifetimes constraints generated at the given program point.
    pub(super) new_lifetime_constraints_at: HashMap<Location, Vec<LifetimeConstraint>>,
}

pub(super) fn compute_lifetimes<'tcx>(
    polonius_input_facts: &AllFacts,
    polonius_output_facts: &PoloniusOutput,
) -> BodyLifetimes {
    let universal_lifetimes = polonius_input_facts.universal_region.iter().map(
        |&region| region.into()
    ).collect();
    let mut universal_lifetime_constraints: Vec<_> = polonius_input_facts.known_subset.iter().map(
        |&(longer, shorter)| {
            LifetimeConstraint { longer: longer.into(), shorter: shorter.into() }
        }
    ).collect();
    universal_lifetime_constraints.sort();

    let lifetimes_starting_at = HashMap::new();
    let lifetimes_ending_at = HashMap::new();
    let new_lifetime_constraints_at = HashMap::new();
    BodyLifetimes {
        universal_lifetimes,
        universal_lifetime_constraints,
        lifetimes_starting_at,
        lifetimes_ending_at,
        new_lifetime_constraints_at,
    }
}

/// The state used in abstract interpretation to compute lifetimes.
struct LifetimeInferenceState {
    /// Polonius input facts.
    input_facts: AllFacts,
}

