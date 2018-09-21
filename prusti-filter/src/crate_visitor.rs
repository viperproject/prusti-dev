use syntax::ast::NodeId;
use rustc::hir;
use rustc::hir::intravisit::{NestedVisitorMap, Visitor};
use rustc::hir::intravisit::*;
use syntax::codemap::Span;
use rustc::ty::TyCtxt;
use validators::Validator;

pub struct CrateVisitor<'tcx: 'a, 'a>
{
    pub crate_name: &'a str,
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub validator: Validator<'a, 'tcx>,
}

impl<'tcx: 'a, 'a> CrateVisitor<'tcx, 'a> {
}

impl<'tcx: 'a, 'a> Visitor<'tcx> for CrateVisitor<'tcx, 'a> {
    fn visit_fn(&mut self, fk: FnKind<'tcx>, fd: &'tcx hir::FnDecl, b: hir::BodyId, s: Span, id: NodeId) {
        let node_path = self.tcx.node_path_str(id);
        //println!("... Checking {}", node_path);

        let procedure_support_status = self.validator.procedure_support_status(fk, fd, b, s, id);
        if procedure_support_status.is_supported() {
            println!( "(*) [procedure] Function {}::{}", self.crate_name, node_path);
            //println!("    - Details: {:?}", fd);
            //println!("    - SUPPORTED")
        } else if procedure_support_status.is_partially_supported() {
            let reasons = procedure_support_status.get_partially_supported_reasons().join(", ");
            println!( "(-) [procedure] Function {}::{}  ({})", self.crate_name, node_path, reasons);
            //println!("    - Details: {:?}", fd);
            //println!("    - Unsupported. Reason: {}", reason)
        } else {
            //println!("( ) [procedure] Function {}::{}", self.crate_name, node_path);
            //println!( "   - {}", procedure_support_status.get_unsupported_reasons().join(", "));
            //println!("    - Details: {:?}", fd);
            //println!("    - Unsupported. Reason: {}", reason)
        }

        let pure_function_support_status = self.validator.pure_function_support_status(fk, fd, b, s, id);
        if pure_function_support_status.is_supported() {
            println!( "(*) [pure fn ] Function {}::{}", self.crate_name, node_path);
            //println!("    - Details: {:?}", fd);
            //println!("    - SUPPORTED")
        } else if pure_function_support_status.is_partially_supported() {
            let reasons = procedure_support_status.get_partially_supported_reasons().join(", ");
            println!( "(-) [pure fn ] Function {}::{}  ({})", self.crate_name, node_path, reasons);
            //println!("    - Details: {:?}", fd);
            //println!("    - Unsupported. Reason: {}", reason)
        } else {
            //println!("( ) [pure fn ] Function {}::{}", self.crate_name, node_path);
            //println!( "   - {}", procedure_support_status.get_unsupported_reasons().join(", "));
            //println!("    - Details: {:?}", fd);
            //println!("    - Unsupported. Reason: {}", reason)
        }

        walk_fn(self, fk, fd, b, s, id);
    }

    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }
}
