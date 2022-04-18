use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_mir_dataflow::{
    impls::{MaybeInitializedPlaces, MaybeUninitializedPlaces},
    move_paths::{MoveData, MovePathIndex},
    Analysis, MoveDataParamEnv, ResultsCursor,
};

pub(super) struct InitializationData<'mir, 'tcx> {
    inits: ResultsCursor<'mir, 'tcx, MaybeInitializedPlaces<'mir, 'tcx>>,
    uninits: ResultsCursor<'mir, 'tcx, MaybeUninitializedPlaces<'mir, 'tcx>>,
}

impl<'mir, 'tcx> InitializationData<'mir, 'tcx> {
    pub(super) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir mir::Body<'tcx>,
        move_env: &'mir MoveDataParamEnv<'tcx>,
    ) -> Self {
        let dead_unwinds = super::elaborate_drops::find_dead_unwinds(tcx, body, move_env);

        let inits = MaybeInitializedPlaces::new(tcx, body, move_env)
            .into_engine(tcx, body)
            .dead_unwinds(&dead_unwinds)
            .pass_name("elaborate_drops")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let uninits = MaybeUninitializedPlaces::new(tcx, body, move_env)
            .mark_inactive_variants_as_uninit()
            .into_engine(tcx, body)
            .dead_unwinds(&dead_unwinds)
            .pass_name("elaborate_drops")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        Self { inits, uninits }
    }
    pub(super) fn seek_before(&mut self, loc: mir::Location) {
        self.inits.seek_before_primary_effect(loc);
        self.uninits.seek_before_primary_effect(loc);
    }

    pub(super) fn maybe_live_dead(&self, path: MovePathIndex) -> (bool, bool) {
        (self.inits.contains(path), self.uninits.contains(path))
    }
}

pub(super) fn create_move_data_param_env<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    def_id: DefId,
) -> MoveDataParamEnv<'tcx> {
    let param_env = tcx.param_env_reveal_all_normalized(def_id);
    let move_data = match MoveData::gather_moves(body, tcx, param_env) {
        Ok(move_data) => move_data,
        Err((_, _)) => {
            unreachable!();
        }
    };
    MoveDataParamEnv {
        move_data,
        param_env,
    }
}
