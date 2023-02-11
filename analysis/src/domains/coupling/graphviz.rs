// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    mir_utils::{mir_kind_at, StatementKinds},
    PointwiseState,
};
use html_escape;
use prusti_rustc_interface::{
    borrowck::consumers::RichLocation,
    middle::{
        mir,
        mir::{BasicBlock, BasicBlockData, Location},
        ty,
        ty::TyCtxt,
    },
    target::abi::VariantIdx,
};
use std::io;

use super::{CouplingOrigins, CouplingState, OriginMap};
use crate::mir_utils::Place;

impl<'facts, 'mir: 'facts, 'tcx: 'mir>
    PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>
{
    // Helper functions: Paramaters for the encoding

    fn graph_global_flags() -> Vec<&'static str> {
        vec![
            "newrank=true;",
            // "nodesep=15;",
            "ranksep=1;",
            "ratio=3;",
            "rankdir=\"TB\";",
            "compound=true;",
            "splines=true;",
            "overlap=false;",
        ]
    }

    fn cluster_block_label(ix: BasicBlock) -> String {
        format!("cluster_block_{:?}", ix)
    }

    fn rich_location_label(rloc: RichLocation) -> String {
        match rloc {
            RichLocation::Start(l) => format!("loc_start_{:?}_{:?}", l.block, l.statement_index),
            RichLocation::Mid(l) => format!("loc_mid_{:?}_{:?}", l.block, l.statement_index),
        }
    }

    fn state_title(state: &CouplingState<'facts, 'mir, 'tcx>, rloc: RichLocation) -> String {
        let locationindex = match rloc {
            RichLocation::Start(l) => state.mir.location_table.start_index(l),
            RichLocation::Mid(l) => state.mir.location_table.mid_index(l),
        }
        .index();
        match rloc {
            RichLocation::Start(l) => format!("Location {:?}: {:?} (Start)", locationindex, l),
            RichLocation::Mid(l) => format!("Location {:?}: {:?} (Mid)", locationindex, l),
        }
    }

    fn statement_formatting_flags() -> String {
        vec![
            "penwidth=2",
            "fillcolor=\"white\"",
            "fontname=\"Courier New\"",
        ]
        .join(" ")
    }

    fn block_formatting_flags() -> String {
        vec![
            "labelloc=\"t\"",
            "fontsize=\"60\"",
            "fontname = \"Courier New\"",
            "labeljust=\"l\"",
            "penwidth=\"8\"",
            // "pencolor=\"blue\"",
        ]
        .join("; ")
    }

    fn internal_edge_flags() -> String {
        vec![
            "weight=\"100\"",
            //"weight=\"1.5\"",
            "fontsize=\"20\"",
            "fontname=\"Courier New\"",
        ]
        .join(", ")
    }

    fn inter_block_edge_flags() -> String {
        vec!["penwidth=\"8\"", "weight=\"1.0\""].join(", ")
    }

    // Start(l) -> Node annotated with MIR at start location
    fn write_mir_edge(
        &self,
        loc: Location,
        to: String,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        writeln!(
            writer,
            "{} -> {} [{}, label=\"{}\"]",
            Self::rich_location_label(RichLocation::Start(loc)),
            to,
            Self::internal_edge_flags(),
            Self::kind_label(mir_kind_at(self.mir, loc))
        )?;
        Ok(())
    }

    fn kind_label(kind: StatementKinds<'mir, 'tcx>) -> String {
        // fixme: make more ergonomic labels for long statements
        match kind {
            StatementKinds::Stmt(sk) => escape_graphviz(format!("{:?}", sk)),
            StatementKinds::Term(tk) => escape_graphviz(format!("{:?}", tk)),
        }
    }

    fn write_regular_statement(
        &self,
        loc: RichLocation,
        state: &CouplingState<'facts, 'mir, 'tcx>,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        self.write_statement(loc, state, Self::state_title(state, loc), writer)
    }

    fn to_kill_to_string(state: &CouplingState<'facts, 'mir, 'tcx>) -> String {
        let mut r = "".to_string();
        for to_kill in state.to_kill.loans.iter() {
            r = format!("{} {:?}", r, to_kill);
        }

        for to_kill in state.to_kill.places.iter().map(|k| format!("{:?} ", k)) {
            r = format!("{} {:?}", r, to_kill);
        }

        if r == "" {
            "none".to_string()
        } else {
            r
        }
    }

    fn write_group(
        group: &OriginMap<'tcx>,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        for (origin, cdgo) in group.iter() {
            writeln!(
                writer,
                "<tr><td align=\"left\">  {:?}</td><td align=\"left\">{}</td></tr>",
                origin,
                html_escape::encode_text(&format!("{:?} --* {:?}", cdgo.leaves(), cdgo.roots())),
            )?;
            for edge in cdgo.edges.iter() {
                writeln!(
                    writer,
                    "<tr><td></td><td align=\"left\">    {} </td></tr>",
                    html_escape::encode_text(&format!(
                        "{:?} -{:?}-> {:?}",
                        edge.lhs, edge.edge, edge.rhs
                    ))
                )?;
            }
        }
        Ok(())
    }

    fn write_statement(
        &self,
        loc: RichLocation,
        state: &CouplingState<'facts, 'mir, 'tcx>,
        title: String,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        writeln!(
            writer,
            "{} [ {}",
            Self::rich_location_label(loc),
            Self::statement_formatting_flags()
        )?;
        // Write out the table here
        writeln!(writer, "shape=\"rectangle\"")?;
        write!(writer, "label=<<table ")?;
        // Table flags
        write!(writer, "border=\"0\" ")?;
        write!(writer, "cellborder=\"0\" ")?;
        write!(writer, "cellpadding=\"4\" ")?;
        writeln!(writer, ">")?;
        // Title row
        writeln!(
            writer,
            "<tr><td bgcolor=\"black\" align=\"center\" colspan=\"2\"><font color=\"white\">{}</font></td></tr>",
            title,
        )?;

        // To kill
        writeln!(
            writer,
            "<tr><td align=\"left\" colspan=\"2\"> to kill: {} </td><td></td></tr>",
            Self::to_kill_to_string(state)
        )?;

        // Groups
        for (ix, group) in state.coupling_graph.origins.origins.iter().enumerate() {
            writeln!(
                writer,
                "<tr><td align=\"left\" colspan=\"2\"> group {:?} </td><td></td></tr>",
                ix
            )?;
            Self::write_group(group, writer)?;
        }

        // writeln!(writer, "<tr><td> content </td></tr>")?;
        writeln!(writer, "</table>>];")?;
        Ok(())
    }

    fn write_ending_node(
        location: Location,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        writeln!(
            writer,
            "{} [{}, shape=\"rectangle\",  label=\"{:?} (end)\"]",
            Self::rich_location_label(RichLocation::Mid(location)),
            Self::statement_formatting_flags(),
            location
        )
    }

    fn write_terminator_out(
        &self,
        block: BasicBlock,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        let loc = self.mir.terminator_loc(block);
        let mut next_states = self
            .lookup_after_block(block)
            .unwrap()
            .iter()
            .map(|(_, st)| st)
            .collect::<Vec<_>>();
        if let Some(state) = next_states.pop() {
            for st in next_states.iter() {
                assert_eq!(&state, st);
            }
            // Writing as a regular statement assuming that assert_eq never fails
            // If for some reason we need flow-dependence at this point, change the line below
            self.write_regular_statement(RichLocation::Mid(loc), state, writer)?
        } else {
            Self::write_ending_node(loc, writer)?;
        }
        Ok(())
    }

    fn write_basic_block(
        &self,
        block_data: &BasicBlockData<'tcx>,
        block: BasicBlock,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        writeln!(writer, "subgraph {} {{", Self::cluster_block_label(block))?;
        writeln!(writer, "{}", Self::block_formatting_flags())?;
        writeln!(writer, "label=\"{:?}\"", block)?;
        for statement_index in 0..block_data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            self.write_regular_statement(
                RichLocation::Start(location),
                self.lookup_before(location).unwrap(),
                writer,
            )?;
            self.write_regular_statement(
                RichLocation::Mid(location),
                self.lookup_after(location).unwrap(),
                writer,
            )?;
        }

        let terminator_location = self.mir.terminator_loc(block);
        self.write_regular_statement(
            RichLocation::Start(terminator_location),
            self.lookup_before(terminator_location).unwrap(),
            writer,
        )?;
        self.write_terminator_out(block, writer)?;

        // Write out edges associated to statements
        for statement_index in 0..=block_data.statements.len() {
            self.write_mir_edge(
                Location {
                    block,
                    statement_index,
                },
                Self::rich_location_label(RichLocation::Mid(Location {
                    block,
                    statement_index,
                })),
                writer,
            )?;
        }

        // Write out edges between statements
        for ix in 0..block_data.statements.len() {
            let loc_from = RichLocation::Mid(Location {
                block,
                statement_index: ix,
            });
            let loc_to = RichLocation::Start(Location {
                block,
                statement_index: (ix + 1),
            });
            writeln!(
                writer,
                "{} -> {} [{}]",
                Self::rich_location_label(loc_from),
                Self::rich_location_label(loc_to),
                Self::statement_formatting_flags()
            )?;
        }

        // write!(writer, "{{rank=same ")?;
        // for ix in 0..block_data.statements.len() {
        //     let loc_s = RichLocation::Start(Location {
        //         block,
        //         statement_index: ix,
        //     });
        //     let loc_m = RichLocation::Mid(Location {
        //         block,
        //         statement_index: ix,
        //     });
        //     write!(writer, "{} ", Self::rich_location_label(loc_s))?;
        //     write!(writer, "{} ", Self::rich_location_label(loc_m))?;
        // }
        // writeln!(writer, "}}")?;

        writeln!(writer, "}}")?;
        Ok(())
    }

    fn write_cfg_edge(
        from: BasicBlock,
        to: BasicBlock,
        writer: &mut dyn io::Write,
    ) -> Result<(), std::io::Error> {
        Ok(())
    }

    pub fn to_graphviz(&self, writer: &mut dyn io::Write) -> Result<(), std::io::Error> {
        writeln!(writer, "digraph CFG {{")?;
        // Write top-level flags
        for f in Self::graph_global_flags().iter() {
            writeln!(writer, "{}", f.to_string())?;
        }

        // Write subgraph for each bb
        for (bbno, bb) in self.mir.basic_blocks.iter_enumerated() {
            self.write_basic_block(bb, bbno, writer)?;
        }

        // Write out the edges between blocks
        for (bbno, block) in self.mir.basic_blocks.iter_enumerated() {
            let end_loc = RichLocation::Mid(self.mir.terminator_loc(bbno));
            for suc in block.terminator().successors() {
                let start_loc = RichLocation::Start(Location {
                    block: suc,
                    statement_index: 0,
                });
                writeln!(
                    writer,
                    "{} -> {} [{}]",
                    Self::rich_location_label(end_loc),
                    Self::rich_location_label(start_loc),
                    Self::inter_block_edge_flags()
                )?
            }
        }

        writeln!(writer, "}}")?;
        Ok(())
    }
}

// Helpers stolen from definitely accessible
fn pretty_print_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: Place<'tcx>,
) -> Option<String> {
    let mut pieces = vec![];

    // Open parenthesis
    for elem in place.projection.iter().rev() {
        match elem {
            mir::ProjectionElem::Deref => pieces.push("(*".to_string()),
            mir::ProjectionElem::Field(..) => pieces.push("(".to_string()),
            _ => {}
        }
    }

    // Skip compiler-generated variables
    if body.local_decls[place.local].from_compiler_desugaring() {
        return None;
    }

    // Find name of the local
    let local_name = body
        .var_debug_info
        .iter()
        .find(|var_debug_info| {
            if let mir::VarDebugInfoContents::Place(debug_place) = var_debug_info.value {
                if let Some(debug_local) = debug_place.as_local() {
                    return debug_local == place.local;
                }
            };
            false
        })
        .map(|var_debug_info| var_debug_info.name);
    if let Some(name) = local_name {
        pieces.push(format!("{}", name));
    } else {
        return None;
    }

    // Close parenthesis
    let mut prev_ty = body.local_decls[place.local].ty;
    let mut variant = None;
    for (proj_base, elem) in place.iter_projections() {
        match elem {
            mir::ProjectionElem::Deref => {
                pieces.push(")".to_string());
            }
            mir::ProjectionElem::Downcast(_, variant_index) => {
                prev_ty = proj_base.ty(body, tcx).ty;
                variant = Some(variant_index);
            }
            mir::ProjectionElem::Field(field, field_ty) => {
                let field_name = describe_field_from_ty(tcx, prev_ty, field, variant)?;
                pieces.push(format!(".{})", field_name));
                prev_ty = field_ty;
                variant = None;
            }
            mir::ProjectionElem::Index(..)
            | mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::OpaqueCast(..)
            | mir::ProjectionElem::Subslice { .. } => {
                // It's not possible to move-out or borrow an individual element.
                unreachable!()
            }
        }
    }

    Some(pieces.join(""))
}

/// End-user visible description of the `field_index`nth field of `ty`
fn describe_field_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    field: mir::Field,
    variant_index: Option<VariantIdx>,
) -> Option<String> {
    if ty.is_box() {
        // If the type is a box, the field is described from the boxed type
        describe_field_from_ty(tcx, ty.boxed_ty(), field, variant_index)
    } else {
        match *ty.kind() {
            ty::TyKind::Adt(def, _) => {
                let variant = if let Some(idx) = variant_index {
                    assert!(def.is_enum());
                    &def.variants()[idx]
                } else {
                    def.non_enum_variant()
                };
                Some(variant.fields[field.index()].ident(tcx).to_string())
            }
            ty::TyKind::Tuple(_) => Some(field.index().to_string()),
            ty::TyKind::Ref(_, ty, _) | ty::TyKind::RawPtr(ty::TypeAndMut { ty, .. }) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Closure(..) | ty::TyKind::Generator(..) => {
                // Supporting these cases is complex
                None
            }
            _ => unreachable!("Unexpected type `{:?}`", ty),
        }
    }
}

fn escape_graphviz(a: String) -> String {
    a.replace("\"", "\\\"")
        .replace("[", "\\[")
        .replace("]", "\\]")
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("<", "\\<")
        .replace(">", "\\>")
        .replace("-", "\\-")
        .replace("\t", "")
        .replace(" ", "")
        .replace("\n", "")
}
