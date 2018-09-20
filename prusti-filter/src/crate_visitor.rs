use syntax::ast::NodeId;
use rustc::hir;
use rustc::hir::intravisit::{NestedVisitorMap, Visitor};
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty::TyCtxt;
use validators::ProcedureValidator;
use validators::SupportStatus;

pub struct CrateVisitor<'tcx: 'a, 'a>
{
    pub crate_name: &'a str,
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub validator: ProcedureValidator<'a, 'tcx>,
}

impl<'tcx: 'a, 'a> CrateVisitor<'tcx, 'a> {
}

impl<'tcx: 'a, 'a> Visitor<'tcx> for CrateVisitor<'tcx, 'a> {
    fn visit_fn(&mut self, fk: FnKind<'tcx>, fd: &'tcx hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) {
        let node_path = self.tcx.node_path_str(id);
        match self.validator.is_supported_fn(fk, fd, b, s, id) {
            SupportStatus::Supported => {
                println!( "(*) Function {}::{}", self.crate_name, node_path);
                //println!("    - Details: {:?}", fd);
                //println!("    - SUPPORTED")
            }
            SupportStatus::Unsupported(reason) => {
                //println!("( ) Function {}::{}", self.crate_name, node_path);
                //println!("    - Details: {:?}", fd);
                //println!("    - Unsupported. Reason: {}", reason)
            }
        }

        walk_fn(self, fk, fd, b, s, id);
    }

    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}
