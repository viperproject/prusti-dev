use task_encoder::TaskEncoder;
use prusti_rustc_interface::{
    middle::ty::GenericArgs,
    span::def_id::DefId
};

/// Task encoders for Rust functions should implement this trait.
pub trait FunctionEnc
    where
        Self: 'static + Sized + TaskEncoder
{
    /// Obtains the function's [`DefId`] from the task key
    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId;

    /// Obtains the caller's [`DefId`] from the task key, if possible
    fn get_caller_def_id(task_key: &Self::TaskKey<'_>) -> Option<DefId>;

    /// Obtains type substitutions for the function. For polymorphic encoding,
    /// this should be the identity substitution obtained from the DefId of the
    /// function. For the monomorphic encoding, the substitutions at the call
    /// site should be used.
    fn get_substs<'tcx>(
        vcx: &vir::VirCtxt<'tcx>,
        substs_src: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx>;
}

/// Implementation for polymorphic encoding
impl <T: 'static + for<'vir> TaskEncoder<TaskKey<'vir> = DefId>> FunctionEnc for T {
    fn get_def_id(task_key: &Self::TaskKey<'_>) -> DefId {
        *task_key
    }

    fn get_caller_def_id(_: &Self::TaskKey<'_>) -> Option<DefId> {
        None
    }

    fn get_substs<'tcx>(
        vcx: &vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> &'tcx GenericArgs<'tcx> {
        GenericArgs::identity_for_item(vcx.tcx(), *def_id)
    }

}
