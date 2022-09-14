use prusti_rustc_interface::{
    dataflow::{
        impls::{MaybeInitializedPlaces, MaybeLiveLocals, MaybeUninitializedPlaces},
        move_paths::MoveData,
        un_derefer::UnDerefer,
        Analysis, MoveDataParamEnv, ResultsCursor,
    },
    middle::{mir, ty::TyCtxt},
};

// FIXME: Remove this file. It is not used anymore.
pub(super) struct InitializationData<'mir, 'tcx> {
    liveness: ResultsCursor<'mir, 'tcx, MaybeLiveLocals>,
    inits: ResultsCursor<'mir, 'tcx, MaybeInitializedPlaces<'mir, 'tcx>>,
    uninits: ResultsCursor<'mir, 'tcx, MaybeUninitializedPlaces<'mir, 'tcx>>,
    move_env: &'mir MoveDataParamEnv<'tcx>,
}

impl<'mir, 'tcx> InitializationData<'mir, 'tcx> {
    pub(super) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir mut mir::Body<'tcx>,
        move_env: &'mir MoveDataParamEnv<'tcx>,
        un_derefer: &'mir UnDerefer<'tcx>,
    ) -> Self {
        // FIXME: Check whether this call is needed.
        super::elaborate_drops::mir_transform::remove_dead_unwinds(tcx, body, move_env, un_derefer);
        let liveness = MaybeLiveLocals
            .into_engine(tcx, body)
            .pass_name("prusti_encoding")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let inits = MaybeInitializedPlaces::new(tcx, body, move_env)
            .into_engine(tcx, body)
            .pass_name("prusti_encoding")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        let uninits = MaybeUninitializedPlaces::new(tcx, body, move_env)
            .mark_inactive_variants_as_uninit()
            .into_engine(tcx, body)
            .pass_name("prusti_encoding")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        Self {
            inits,
            uninits,
            liveness,
            move_env,
        }
    }
    pub(super) fn seek_before(&mut self, loc: mir::Location) {
        self.liveness.seek_before_primary_effect(loc);
        self.inits.seek_before_primary_effect(loc);
        self.uninits.seek_before_primary_effect(loc);
    }
    pub(super) fn is_local_initialized_and_alive(&self, local: mir::Local) -> bool {
        let path = self.move_env.move_data.rev_lookup.find_local(local);
        self.liveness.get().contains(local)
            && self.inits.get().contains(path)
            && self.uninits.get().contains(path)
    }
}

pub(super) fn create_move_data_param_env_and_un_derefer<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> (MoveDataParamEnv<'tcx>, UnDerefer<'tcx>) {
    let def_id = body.source.def_id();
    let param_env = tcx.param_env_reveal_all_normalized(def_id);
    let (side_table, move_data) = match MoveData::gather_moves(body, tcx, param_env) {
        Ok(move_data) => move_data,
        Err((move_data, _)) => {
            tcx.sess.delay_span_bug(
                body.span,
                "No `move_errors` should be allowed in MIR borrowck",
            );
            (Default::default(), move_data)
        }
    };
    let un_derefer = UnDerefer {
        tcx,
        derefer_sidetable: side_table,
    };
    let env = MoveDataParamEnv {
        move_data,
        param_env,
    };
    (env, un_derefer)
}
