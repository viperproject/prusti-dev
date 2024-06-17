// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::utils::Place;
use std::{
    fs::File,
    io::{self, Write},
    rc::Rc,
};

use super::{CapabilityLocal, CapabilitySummary};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowSet,
        consumers::{
            calculate_borrows_out_of_scope_at_location, BorrowIndex, Borrows, LocationTable,
            PoloniusInput, PoloniusOutput, RegionInferenceContext,
        },
    },
    data_structures::fx::{FxHashMap, FxIndexMap},
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{Body, Local, Location, Promoted, RETURN_PLACE, TerminatorKind, UnwindAction},
        ty::{self, GenericArgsRef, ParamEnv, RegionVid, TyCtxt},
    },
};
use serde::Serialize;

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
#[derive(Serialize)]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Serialize)]
struct MirNode {
    id: String,
    label: String,
}

#[derive(Serialize)]
struct MirEdge {
    source: String,
    target: String,
    label: String,
}

fn mk_mir_graph(body: &Body<'_>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let mut label = String::new();
        label.push_str(
            &format!(
                r#"<table data-bb="bb{}" border="1" cellspacing="0" cellpadding="4" style="border-collapse: collapse;">"#,
                bb.as_usize()
            )
        );
        label.push_str(&format!(
            "<tr><td>(on start)</td><td><b>BB{}</b></td></tr>",
            bb.as_usize()
        ));

        for (i, stmt) in data.statements.iter().enumerate() {
            label.push_str(&format!(
                "<tr data-bb=\"{}\" data-statement=\"{}\"><td>{}</td> <td>{:?}</td></tr>",
                bb.as_usize(),
                i,
                i,
                stmt
            ));
        }

        label.push_str(&format!(
            "<tr><td>T</td> <td>{:?}</td></tr>",
            data.terminator().kind
        ));
        label.push_str("<tr><td>(on end)</td></tr>");
        label.push_str("</table>");

        nodes.push(MirNode {
            id: format!("{:?}", bb),
            label,
        });

        match &data.terminator().kind {
            TerminatorKind::Goto { target } => todo!(),
            TerminatorKind::SwitchInt { discr, targets } => todo!(),
            TerminatorKind::UnwindResume => {}
            TerminatorKind::UnwindTerminate(_) => todo!(),
            TerminatorKind::Return => {}
            TerminatorKind::Unreachable => todo!(),
            TerminatorKind::Drop { place, target, unwind, replace } => todo!(),
            TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } => todo!(),
            TerminatorKind::Assert { cond, expected, msg, target, unwind } => {
                match unwind {
                    UnwindAction::Continue => todo!(),
                    UnwindAction::Unreachable => todo!(),
                    UnwindAction::Terminate(_) => todo!(),
                    UnwindAction::Cleanup(cleanup) => {
                        edges.push(MirEdge {
                            source: format!("{:?}", bb),
                            target: format!("{:?}", cleanup),
                            label: format!("unwind"),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{:?}", bb),
                    target: format!("{:?}", target),
                    label: format!("success"),
                });
            }
            TerminatorKind::Yield { value, resume, resume_arg, drop } => todo!(),
            TerminatorKind::GeneratorDrop => todo!(),
            TerminatorKind::FalseEdge { real_target, imaginary_target } => todo!(),
            TerminatorKind::FalseUnwind { real_target, unwind } => todo!(),
            TerminatorKind::InlineAsm { template, operands, options, line_spans, destination, unwind } => todo!(),
        }
    }

    MirGraph { nodes, edges }
}

pub fn generate_json_from_mir(body: &Body<'_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(body);
    let mut file = File::create("visualization/mir_output.json")?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}

pub fn generate_dot_graph(
    location: Location,
    summary: &CapabilitySummary,
    borrow_set: &BorrowSet,
    input_facts: &PoloniusInput,
    file_path: &str,
) -> io::Result<()> {
    let mut file = File::create(file_path)?;
    writeln!(file, "digraph CapabilitySummary {{")?;
    writeln!(file, "node [shape=rect]")?;

    for (local, capability) in summary.iter().enumerate() {
        match capability {
            CapabilityLocal::Unallocated => {
            }
            CapabilityLocal::Allocated(projections) => {
                for (place, kind) in projections.iter() {
                    writeln!(
                        file,
                        "    \"{:?}\" [label=\"{:?} {:?}\"];",
                        place, place, kind
                    )?;
                }
            }
        }
    }
    for (borrow_location, borrow_data) in borrow_set.location_map.iter() {
        let from = format!("{:?}", borrow_data.borrowed_place);
        let to = format!("{:?}", borrow_data.assigned_place);
        eprintln!("{} BORROWED: {} {}", file_path, from, to);
        writeln!(file, "    \"{}\" -> \"{}\" [label=\"Borrow\"];", from, to)?;
    }

    writeln!(file, "}}");
    Ok(())
}
