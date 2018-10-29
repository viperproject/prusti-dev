use syntax::ast::NodeId;
use rustc::hir;
use syntax::print::pprust;
use rustc::hir::intravisit::{NestedVisitorMap, Visitor};
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty::TyCtxt;
use validators::Validator;
use validators::SupportStatus;
use std::rc::Rc;
use syntax::source_map::SourceMap;
use prusti_interface::environment::{ProcedureLoops, Procedure};

pub struct CrateVisitor<'tcx: 'a, 'a>
{
    pub crate_name: &'a str,
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub validator: Validator<'a, 'tcx>,
    pub crate_status: CrateStatus,
    pub source_map: Rc<SourceMap>,
}

#[derive(Serialize, Deserialize)]
pub struct CrateStatus {
    pub crate_name: String,
    pub functions: Vec<FunctionStatus>,
}

#[derive(Serialize, Deserialize)]
pub struct FunctionStatus {
    pub crate_name: String,
    pub node_path: String,
    pub procedure: SupportStatus,
    pub pure_function: SupportStatus,
    pub lines_of_code: usize,
    pub num_loop_heads: usize,
    pub max_loop_nesting: usize,
    pub source_code: Option<String>,
}

impl<'tcx: 'a, 'a> CrateVisitor<'tcx, 'a> {
}

impl<'tcx: 'a, 'a> Visitor<'tcx> for CrateVisitor<'tcx, 'a> {
    fn visit_fn(&mut self, fk: FnKind<'tcx>, fd: &'tcx hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) {
        let node_path = self.tcx.node_path_str(id);
        debug!("Checking {}", node_path);

        let procedure_support_status = self.validator.procedure_support_status(fk, fd, b, s, id);
        let pure_function_support_status = self.validator.pure_function_support_status(fk, fd, b, s, id);

        let def_id = self.tcx.hir.local_def_id(id);
        let procedure = Procedure::new(self.tcx, def_id);
        let loop_info = ProcedureLoops::new(procedure.get_mir());
        let num_loop_heads = loop_info.count_loop_heads();
        let max_loop_nesting = loop_info.max_loop_nesting();

        let lines_of_code = s.end().line - s.start().line + 1;
        let source_code = self.source_map.span_to_string(s);
        let show_source_code = procedure_support_status.is_supported() || pure_function_support_status.is_supported();

        let function_status = FunctionStatus {
            crate_name: String::from(self.crate_name),
            node_path: node_path,
            procedure: procedure_support_status,
            pure_function: pure_function_support_status,
            lines_of_code,
            num_loop_heads,
            max_loop_nesting,
            source_code: if show_source_code { Some(source_code) } else { None }
        };
        self.crate_status.functions.push(function_status);

        walk_fn(self, fk, fd, b, s, id);
    }

    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}
