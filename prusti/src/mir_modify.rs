
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{
        mir::{visit::MutVisitor, Body, Operand, Location, Constant,
        ConstantKind, BasicBlock, BasicBlockData},
        mir::interpret::{Scalar, ConstValue},
        ty::{self, TyCtxt, ScalarInt},
    },
    span::def_id::LocalDefId,
};


/// Compute the main MIR body and the list of MIR bodies of the promoteds.
pub(crate) fn mir_built(
    tcx: TyCtxt<'_>,
    def: ty::WithOptConstParam<LocalDefId>,
) -> &Steal<Body<'_>> {
    // is it our job to store it?
    println!("mir built is called");
    let steal = ((*DEFAULT_QUERY_PROVIDERS).mir_built)(tcx, def);
    let mut stolen = steal.steal();

    let mut visitor = InsertChecksVisitor { tcx };
    visitor.visit_body(&mut stolen);

    tcx.alloc_steal_mir(stolen)
}

struct InsertChecksVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for InsertChecksVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        println!("Mir body: {:#?}", body);
        self.super_body(body);
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &mut BasicBlockData<'tcx>) {
        self.super_basic_block_data(block, data);
    }

    fn visit_operand(&mut self, operand: &mut Operand<'tcx>, location: Location) {
        match operand {
            Operand::Constant(box c) => {
                if let Constant{ literal, .. } = c {
                    if let ConstantKind::Val(value, ty) = literal {
                        if ty.is_bool() {
                            println!("found a boolean constant!");
                            *value = ConstValue::Scalar(Scalar::Int(ScalarInt::FALSE))
                        }
                    }
                }
            },
            _ => {}
        }
        self.super_operand(operand, location);
    }
}
