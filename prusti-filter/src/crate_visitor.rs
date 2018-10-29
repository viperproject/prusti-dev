use syntax::ast::NodeId;
use rustc::hir;
use rustc::hir::intravisit::{NestedVisitorMap, Visitor};
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty::TyCtxt;
use validators::Validator;
use validators::SupportStatus;

pub struct CrateVisitor<'tcx: 'a, 'a>
{
    pub crate_name: &'a str,
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub validator: Validator<'a, 'tcx>,
    pub crate_status: CrateStatus,
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
}

impl<'tcx: 'a, 'a> CrateVisitor<'tcx, 'a> {
}

impl<'tcx: 'a, 'a> Visitor<'tcx> for CrateVisitor<'tcx, 'a> {
    fn visit_fn(&mut self, fk: FnKind<'tcx>, fd: &'tcx hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) {
        let node_path = self.tcx.node_path_str(id);
        debug!("Checking {}", node_path);

        let procedure_support_status = self.validator.procedure_support_status(fk, fd, b, s, id);
        let pure_function_support_status = self.validator.pure_function_support_status(fk, fd, b, s, id);

        let function_status = FunctionStatus {
            crate_name: String::from(self.crate_name),
            node_path: node_path,
            procedure: procedure_support_status,
            pure_function: pure_function_support_status,
        };
        self.crate_status.functions.push(function_status);

        walk_fn(self, fk, fd, b, s, id);
    }

    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}
