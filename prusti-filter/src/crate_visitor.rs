// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::{Procedure, ProcedureLoops, Environment};
use rustc::hir;
use rustc::hir::intravisit::*;
use rustc::hir::intravisit::{NestedVisitorMap, Visitor};
use rustc::ty::TyCtxt;
use syntax::ast::NodeId;
use syntax::codemap::Span;
use validators::SupportStatus;
use validators::Validator;

pub struct CrateVisitor<'r, 'a: 'r, 'tcx: 'a> {
    pub crate_name: &'a str,
    pub tcx: TyCtxt<'tcx>,
    pub env: &'r Environment<'r, 'a, 'tcx>,
    pub validator: Validator<'a, 'tcx>,
    pub crate_status: CrateStatus,
}

#[derive(Serialize)]
pub struct CrateStatus {
    pub crate_name: String,
    pub functions: Vec<FunctionStatus>,
}

#[derive(Serialize)]
pub struct FunctionStatus {
    pub crate_name: String,
    pub node_path: String,
    pub has_pure_attr: bool,
    pub procedure: SupportStatus,
    pub pure_function: SupportStatus,
    pub lines_of_code: usize,
    pub num_basic_blocks: usize,
    pub num_encoded_basic_blocks: usize,
    pub num_loop_heads: usize,
    pub max_loop_nesting: usize,
    pub from_macro_expansion: bool,
    pub source_code: Option<String>,
}

impl<'r, 'a: 'r, 'tcx: 'a> CrateVisitor<'r, 'a, 'tcx> {}

impl<'r, 'a: 'r, 'tcx: 'a> Visitor<'tcx> for CrateVisitor<'r, 'a, 'tcx> {
    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx hir::FnDecl,
        b: hir::BodyId,
        s: Span,
        id: NodeId,
    ) {
        let def_id = self.tcx.hir.local_def_id(id);
        let procedure = Procedure::new(self.tcx, def_id);
        let node_path = procedure.get_def_path();
        debug!("Checking {}", node_path);

        let procedure_support_status = self.validator.procedure_support_status(def_id);
        let pure_function_support_status = self.validator.pure_function_support_status(def_id);

        let num_basic_blocks = procedure.get_all_cfg_blocks().len();
        let num_encoded_basic_blocks = procedure.get_reachable_nonspec_cfg_blocks().len();
        let loop_info = ProcedureLoops::new(procedure.get_mir());
        let num_loop_heads = loop_info.count_loop_heads();
        let max_loop_nesting = loop_info.max_loop_nesting();

        let from_macro_expansion = s.parent().is_some();
        let source_code = self.env.codemap().span_to_snippet(s).unwrap();
        let lines_of_code = source_code.lines().count();
        let show_source_code =
            procedure_support_status.is_supported() || pure_function_support_status.is_supported();

        let function_status = FunctionStatus {
            crate_name: String::from(self.crate_name),
            node_path: node_path,
            has_pure_attr: self.env.has_attribute_name(def_id, "pure"),
            procedure: procedure_support_status,
            pure_function: pure_function_support_status,
            lines_of_code,
            num_basic_blocks,
            num_encoded_basic_blocks,
            num_loop_heads,
            max_loop_nesting,
            from_macro_expansion,
            source_code: if show_source_code {
                Some(source_code)
            } else {
                None
            },
        };
        self.crate_status.functions.push(function_status);

        walk_fn(self, fk, fd, b, s, id);
    }

    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}
