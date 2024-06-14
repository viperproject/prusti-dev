// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fs::File;
use std::io::{self, Write};
use std::rc::Rc;
use crate::utils::Place;

use super::{CapabilityLocal, CapabilitySummary};
use prusti_rustc_interface::{
    borrowck::consumers::{BorrowIndex, Borrows, calculate_borrows_out_of_scope_at_location},
    borrowck::borrow_set::BorrowSet,
    borrowck::consumers::{PoloniusInput, RegionInferenceContext, LocationTable, PoloniusOutput},
    data_structures::fx::FxHashMap,
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    data_structures::fx::FxIndexMap,
    middle::{
        mir::{Body, Location, Promoted, RETURN_PLACE, Local},
        ty::{self, RegionVid, TyCtxt, GenericArgsRef, ParamEnv},
    },
};

impl<'tcx> CapabilityLocal<'tcx> {
    pub fn to_dot(&self, local: usize, file: &mut File) -> io::Result<()> {
        match self {
            CapabilityLocal::Unallocated => {
                writeln!(file, "    {} [label=\"Unallocated\"];", local)?;
            }
            CapabilityLocal::Allocated(projections) => {
                for (place, kind) in projections.iter() {
                    writeln!(file, "    {} -> {:?} [label=\"{:?}\"];", local, place, kind)?;
                }
            }
        }
        Ok(())
    }
}

pub fn generate_dot_graph(summary: &CapabilitySummary, polonius_facts: Rc<PoloniusOutput>, file_path: &str) -> io::Result<()> {
    let mut file = File::create(file_path)?;
    writeln!(file, "digraph CapabilitySummary {{")?;
    writeln!(file, "node [shape=rect]")?;

    for (local, capability) in summary.iter().enumerate() {
        match capability {
            CapabilityLocal::Unallocated => {
                writeln!(file, "    {} [label=\"Unallocated\"];", local)?;
            }
            CapabilityLocal::Allocated(projections) => {
                for (place, kind) in projections.iter() {
                    writeln!(file, "    \"{:?}\" [label=\"{:?} {:?}\"];", place, place, kind)?;
                }
            }
        }
    }

    writeln!(file, "}}");
    Ok(())
}
