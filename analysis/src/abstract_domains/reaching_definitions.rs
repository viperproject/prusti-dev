// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides the reaching definitions analysis state for MIR.
//!
//! For each program point it stores which assignments to local
//! variables MAY reach that program point.
//! derived from mir_analyses/liveness

use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::AbstractState;
use rustc_middle::mir;


/*#[derive(PartialEq, Eq, Hash, Copy, Clone, Ord, PartialOrd)]
pub struct Assignment {
    pub target: mir::Local,
    pub location: mir::Location,
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}={:?}", self.target, self.location)
    }
}*/

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct ReachingDefsState {
    reaching_assignments: HashMap<mir::Local, HashSet<mir::Location>>,
}

impl<'tcx> AbstractState<'tcx> for ReachingDefsState {
    fn new_bottom() -> Self {
        Self {
            reaching_assignments: HashMap::new(),
        }
    }

    fn new_initial(args: &[mir::LocalDecl<'tcx>]) -> Self {
        new_bottom()
    }

    fn widening_threshold() -> u32 {
        7
    }

    fn join(&mut self, other: &Self) {
        for (local, other_assignments) in other.reaching_assignments.iter() {
            let assignments = self.reaching_assignments.entry(local).or_insert(HashSet::new());
            for assignment in other_assignments.iter() {
                assignments.insert(assignment);
            }
        }
    }

    fn widen(&mut self, previous: &Self) {
        // assignments are static info -> cannot grow infinitely -> widening should not be needed
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location, stmt: &mir::Statement<'tcx>){
        match statement.kind {
            mir::StatementKind::Assign(box (ref target, _)) => {
                if let Some(local) = target.as_local() {
                    let assignment_set = self.reaching_assignments.entry(local).or_insert(HashSet::new());
                    assignment_set.clear();
                    assignment_set.insert(location);
                }
            }
            _ => {}
        }
    }

    fn apply_terminator_effect(&self, location: &mir::Location, terminator: &mir::terminator::Terminator<'tcx>) -> Vec<(mir::BasicBlock, Self)> {
        match terminator.kind {
            mir::TerminatorKind::Call {
                ref destination, ..     //TODO: need to handle cleanup?
            } => {
                if let Some((place, bb)) = destination {
                    let mut dest_state = self.clone();
                    if let Some(local) = place.as_local() {
                        let assignment_set = dest_state.reaching_assignments.entry(local).or_insert(HashSet::new());
                        assignment_set.clear();
                        assignment_set.insert(location);
                    }
                    return Vec::from([(bb, dest_state)]);
                }
            }
            _ => {}
        }

        Vec::new()
    }
}
