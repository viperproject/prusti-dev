use std::ops::Index;

use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::{
    encoders::{
        ty_impure::{TyImpureEnc, TyImpureEncOutputRef}
    },
    trait_support::is_function_with_body,
};

pub struct MirLocalDefEnc;

#[derive(Clone, Debug)]
pub struct MirLocalDefEncOutputRef {
    pub arg_count: usize,
}
impl task_encoder::OutputRefAny for MirLocalDefEncOutputRef {}

#[derive(Clone, Copy)]
pub struct MirLocalDefEncOutput<'vir> {
    pub locals: &'vir IndexVec<mir::Local, LocalDef<'vir>>,
    pub arg_count: usize,
}
pub type MirLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::LocalRef<'vir>,
    pub local_snap: vir::LocalSnap<'vir>,
    pub local_ex: vir::ExprRef<'vir>,
    pub impure_snap: vir::ExprSnap<'vir>,
    pub impure_pred: vir::ExprBool<'vir>,
    pub ty: &'vir TyImpureEncOutputRef<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'vir> = (
        DefId,                    // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // ID of the caller function, if any
        bool,                     // `true` = include non-argument locals (if available)
    );

    type OutputRef<'vir> = MirLocalDefEncOutputRef;

    type OutputFullLocal<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, substs, caller_def_id, all_locals) = *task_key;

        fn mk_local_def<'vir>(
            vcx: &'vir vir::VirCtxt<'vir>,
            name: &'vir str,
            ty: TyImpureEncOutputRef<'vir>,
        ) -> LocalDef<'vir> {
            let local = vcx.mk_local(name, vir::TYPE_REF);
            let local_snap = vcx.mk_local(name, ty.snapshot());
            let local_ex = vcx.mk_local_ex_local(local);
            let impure_snap = ty.ref_to_snap(vcx, local_ex);
            let impure_pred = ty.ref_to_pred(vcx, local_ex, None);
            LocalDef {
                local,
                local_snap,
                local_ex,
                impure_snap,
                impure_pred,
                ty: vcx.alloc(ty),
            }
        }

        let trusted = crate::encoders::spec::is_function_trusted(def_id, substs);
        vir::with_vcx(|vcx| {
            // TODO: refactor this a bit: split into one encoder for arguments (only)
            //   and one for locals (only)
            let data = if !trusted
                && let Some(local_def_id) = def_id.as_local()
                && is_function_with_body(vcx.tcx(), def_id)
            {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                deps.emit_output_ref(*task_key, MirLocalDefEncOutputRef {
                    arg_count: body.arg_count,
                })?;
                let locals = IndexVec::from_fn_n(
                    |arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}p", arg.index());
                        let ty = deps
                            .require_local::<TyImpureEnc>(body.local_decls[arg].ty)
                            .unwrap();
                        mk_local_def(vcx, local, ty)
                    },
                    if all_locals {
                        body.local_decls.len()
                    } else {
                        // return + arguments
                        1 + body.arg_count
                    },
                );
                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: body.arg_count,
                }
            } else {
                let typing_env =
                    ty::TypingEnv::post_analysis(vcx.tcx(), caller_def_id.unwrap_or(def_id));
                let sig = vcx.tcx().instantiate_and_normalize_erasing_regions(
                    substs,
                    typing_env,
                    vcx.tcx().fn_sig(def_id),
                );
                let sig = sig.skip_binder();
                deps.emit_output_ref(*task_key, MirLocalDefEncOutputRef {
                    arg_count: sig.inputs().len(),
                })?;

                let locals = (0..sig.inputs_and_output.len())
                    .map(mir::Local::from)
                    .map(|arg: mir::Local| {
                        let local = vir::vir_format!(vcx, "_{}p", arg.index());
                        let ty = if arg.index() == 0 {
                            sig.output()
                        } else {
                            sig.inputs()[arg.index() - 1]
                        };
                        let ty = deps.require_local::<TyImpureEnc>(ty)?;
                        Ok(mk_local_def(vcx, local, ty))
                    })
                    .collect::<Result<IndexVec<_, _>, _>>()?;

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok((data, ()))
        })
    }
}

impl<'vir> Index<mir::Local> for MirLocalDefEncOutput<'vir> {
    type Output = LocalDef<'vir>;
    fn index(&self, index: mir::Local) -> &Self::Output {
        &self.locals[index]
    }
}
