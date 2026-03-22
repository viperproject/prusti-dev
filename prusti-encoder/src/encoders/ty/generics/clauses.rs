use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc, r#trait::TraitEnc},
};

/// Encodes clauses as a viper expression.
///
/// ### Example
/// `GParams([T], [T: Iterator<Item = i32>])` will be encoded as
/// `Iterator_impl(T) && Iterator_assoc_type_Item(T) == i32_type()`
pub struct ClausesEnc;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClausesEncTask<'tcx> {
    /// The GParams that provides the bounds to encode
    pub gparams: GParams<'tcx>,
    /// Substitutions to apply to the bounds
    pub substs: ty::GenericArgsRef<'tcx>,
}

impl TaskEncoder for ClausesEnc {
    task_encoder::encoder_cache!(ClausesEnc);

    const ENCODER_NAME: &'static str = "clauses encoder";

    type TaskDescription<'vir> = ClausesEncTask<'vir>;

    type OutputFullDependency<'vir> = vir::ExprBool<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let clauses = task_key.gparams.typing_env().param_env.caller_bounds();

        let mut checks = Vec::new();

        vir::with_vcx(|vcx| {
            for clause in clauses {
                let clause = ty::EarlyBinder::bind(clause).instantiate(vcx.tcx(), task_key.substs);

                match clause.kind().skip_binder() {
                    ty::ClauseKind::Trait(trait_pred) => {
                        let trait_ = deps.require_ref::<TraitEnc>(trait_pred.def_id()).unwrap();

                        let args = deps
                            .require_dep::<GArgsTyEnc>(GArgs::new(
                                task_key.gparams,
                                trait_pred.trait_ref.args,
                            ))
                            .unwrap();

                        let impl_check = (trait_.impl_fun)(args.get_ty(), args.get_const());
                        checks.push(impl_check);
                    }
                    ty::ClauseKind::Projection(proj_pred) => {
                        let trait_ = deps
                            .require_ref::<TraitEnc>(proj_pred.trait_def_id(vcx.tcx()))
                            .unwrap();

                        let args = deps
                            .require_dep::<GArgsTyEnc>(GArgs::new(
                                task_key.gparams,
                                proj_pred.projection_term.args,
                            ))
                            .unwrap();

                        match proj_pred.term.kind() {
                            ty::TermKind::Ty(ty) => {
                                let projection = trait_.assoc_types[&proj_pred.def_id()](
                                    args.get_ty(),
                                    args.get_const(),
                                );
                                let decomp = RustTyDecomposition::from_ty(ty, task_key.gparams);
                                let gparams = deps
                                    .require_dep::<GenericParamsEnc>(task_key.gparams)
                                    .unwrap();
                                let ty_expr = gparams.ty_expr(deps, decomp);
                                checks.push(vcx.mk_eq_expr(projection, ty_expr));
                            }
                            ty::TermKind::Const(_) => {
                                todo!("Implement const projections")
                            }
                        }
                    }
                    clause => unimplemented!("Encoding a {clause:?} is not yet supported"),
                }
            }
            Ok(((), vcx.mk_conj(&checks)))
        })
    }
}
