/// Results of MIR dataflow analyses.

use std::collections::HashMap;
use std::mem::transmute;

use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc::mir;
use rustc_mir::borrow_check::{MirBorrowckCtxt, do_mir_borrowck};
use rustc_mir::borrow_check::flows::Flows;
use rustc_mir::dataflow::FlowsAtLocation;
use rustc_mir::dataflow::move_paths::HasMoveData;

/// Stores the results of MIR dataflow analyses.
///
/// Note that MIR dataflow analyses tracks only local variables and
/// places that matter. For example, if `_2.0.1` is never accessed in
/// the program, it will not be tracked by the flow analysis.
struct MirDataflowInfo<'tcx> {
    /// Places that are maybe initialized at each program point.
    pub maybe_init: HashMap<mir::Location, Vec<mir::Place<'tcx>>>,
    pub maybe_uninit: HashMap<mir::Location, Vec<mir::Place<'tcx>>>,
}

/// A querable interface to MIR dataflow analysis results.
pub struct DataflowInfo<'tcx> {
    mir_info: MirDataflowInfo<'tcx>,
}

impl<'tcx> DataflowInfo<'tcx> {

    pub fn get_maybe_uninit_at(&mut self, location: mir::Location) -> &Vec<mir::Place<'tcx>> {
        self.mir_info.maybe_uninit.get(&location).unwrap()
    }
}

static mut data: Option<MirDataflowInfo<'static>> = None;

/// This function uses global mutable state and it should not be invoked
/// concurrently.
pub fn construct_dataflow_info<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId,
                                         mir: &mir::Mir<'tcx>) -> DataflowInfo<'tcx> {
    debug!("Def id = {:?}", def_id);
    assert!(tcx.nll());
    let opt_closure_req = tcx.infer_ctxt().enter(|infcx| {
        do_mir_borrowck(&infcx, mir, def_id, Some(box callback))
    });
    let mir_info = unsafe {
        transmute::<MirDataflowInfo<'static>, MirDataflowInfo<'tcx>>(data.take().unwrap())
    };
    DataflowInfo {
        mir_info: mir_info,
    }
}

/// Information we use:
///
/// +   From `Flows`:
///
///     1.  `inits` – what places are maybe initialized;
///     2.  `uninits` – what places are maybe uninitialized.
///
fn callback<'s, 'g, 'gcx, 'tcx>(mbcx: &'s mut MirBorrowckCtxt<'g, 'gcx, 'tcx>, flows: &'s mut Flows<'g, 'gcx, 'tcx>) {

    let mut dataflow_info = MirDataflowInfo::<'tcx> {
        maybe_init: HashMap::new(),
        maybe_uninit: HashMap::new(),
    };


    for bb in mbcx.mir.basic_blocks().indices() {

        flows.reset_to_entry_of(bb);

        let mir::BasicBlockData { ref statements, ref terminator, is_cleanup: _ } =
            mbcx.mir[bb];
        let mut location = mir::Location { block: bb, statement_index: 0 };

        let terminator_index = statements.len();

        while location.statement_index <= terminator_index {
            if location.statement_index < terminator_index {
                flows.reconstruct_statement_effect(location);
            } else {
                flows.reconstruct_terminator_effect(location);
            }
            flows.apply_local_effect(location);

            let mut maybe_init = Vec::new();
            let mut maybe_uninit = Vec::new();

            flows.inits.each_state_bit(|mpi_init| {
                let move_data = &flows.inits.operator().move_data();
                let move_path = &move_data.move_paths[mpi_init];
                let place = &move_path.place;
                maybe_init.push(place.clone());
            });
            dataflow_info.maybe_init.insert(location, maybe_init);

            flows.uninits.each_state_bit(|mpi_uninit| {
                let move_data = &flows.uninits.operator().move_data();
                let move_path = &move_data.move_paths[mpi_uninit];
                let place = &move_path.place;
                maybe_uninit.push(place.clone());
            });
            dataflow_info.maybe_uninit.insert(location, maybe_uninit);

            location.statement_index += 1;
        }
    }

    unsafe {
        let dataflow_info = transmute::<MirDataflowInfo<'tcx>, MirDataflowInfo<'static>>(dataflow_info);
        data = Some(dataflow_info);
    }
}
