use crate::modify_mir::mir_info_collector::MirInfo;
use prusti_interface::{environment::EnvQuery, utils};
use prusti_rustc_interface::{
    middle::{
        mir::{self, visit::MutVisitor},
        ty::{self, TyCtxt},
    },
    span::{def_id::DefId, DUMMY_SP},
};

pub(crate) struct PredicateReplacer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    env_query: EnvQuery<'tcx>,
    body_info: &'a MirInfo<'tcx>,
    is_check_fn: bool,
}

impl<'tcx, 'a> PredicateReplacer<'tcx, 'a> {
    /// If any check function calls a predicate, we want to replace it with
    /// a call to the check function that is generated for that predicate
    pub(crate) fn run(
        tcx: TyCtxt<'tcx>,
        body_info: &'a MirInfo<'tcx>,
        def_id: DefId,
        body: &mut mir::Body<'tcx>,
    ) {
        // 1. figure out if this itself is a check function:
        let env_query = EnvQuery::new(tcx);
        let is_check_fn = utils::has_check_only_attr(env_query.get_attributes(def_id));
        let mut replacer = Self {
            tcx,
            env_query,
            body_info,
            is_check_fn,
        };
        replacer.visit_body(body);
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for PredicateReplacer<'tcx, 'a> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        if let mir::TerminatorKind::Call { func, .. } = &mut terminator.kind {
            if !self.is_check_fn && !self.body_info.check_blocks.contains(&location.block) {
                // If predciates are called outside of check blocks or functions, this is none
                // of our business here. This might be inside a spec function (which is legal)
                // or in the worse case, in normal user code, but this doesnt need to
                // be handled here.
                return;
            }
            if let Some((call_id, generics)) = func.const_fn_def() {
                // check if the called function is a predicate, and also if it has
                let attrs = self.env_query.get_attributes(call_id);
                if !utils::has_prusti_attr(attrs, "pred_spec_id_ref") {
                    // not a predicate, nothing to be done
                    return;
                }
                if let Some(check_id) = self.body_info.specs.get_predicate_check(&call_id) {
                    let func_ty = self
                        .tcx
                        .mk_ty_from_kind(ty::TyKind::FnDef(check_id, generics));
                    let check_func = mir::Operand::Constant(Box::new(mir::Constant {
                        span: DUMMY_SP,
                        user_ty: None,
                        literal: mir::ConstantKind::zero_sized(func_ty),
                    }));
                    // replace the call to the predicate with the call to the
                    // runtime checked predicate
                    *func = check_func;
                } else {
                    // if we don't panic here, this will lead to a panic at runtime
                    // stating that the predicate has no body. Better?
                    panic!("Tried to execute a predicate in a runtime check, but for predicates to be exeuctable they need to be marked with #[insert_runtime_check]");
                }
            }
        }
    }
}
