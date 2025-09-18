use std::ops::Index;

use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty},
    span::def_id::DefId,
};

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::HasType;

use crate::{
    encoders::{ty::{use_impure::TyUseImpure, RustTyDecomposition}, TyUseImpureEnc}, trait_support::is_function_with_body
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

impl<'vir> MirLocalDefEncOutput<'vir> {
    /// Returns the definitions for the function return value.
    pub fn ret(&self) -> LocalDef<'vir> {
        self[mir::RETURN_PLACE]
    }

    /// The snapshot type of the fn return value. Used to construct e.g. the
    /// `FunctionIdn`.
    pub fn snap_ty_return(&self) -> vir::TypeSnap<'vir> {
        self.ret().local_snap.ty()
    }

    fn arg_locals(&self) -> impl Iterator<Item = mir::Local> + '_ {
        (1..=self.arg_count).map(mir::Local::from)
    }

    /// Creates an iterator of all fn arguments. Can be used to construct e.g.
    /// type assertions.
    pub fn args(&self) -> impl Iterator<Item = LocalDef<'vir>> + '_ {
        self.arg_locals().map(|local| self[local])
    }

    /// Creates an iterator of the snapshot type of all fn arguments. Used to
    /// construct e.g. the `FunctionIdn`.
    pub fn snap_ty_args(&self) -> impl Iterator<Item = vir::TypeSnap<'vir>> + '_ {
        self.args().map(|arg| arg.local_snap.ty())
    }

    /// Creates an iterator of the snapshot type of all fn arguments. Used to
    /// construct e.g. the `FunctionIdn`.
    pub fn local_decl_args(&self) -> impl Iterator<Item = vir::LocalDeclSnap<'vir>> + '_ {
        self.args().map(|arg| arg.local_snap)
    }
}

pub type MirLocalDefEncError = ();

#[derive(Clone, Copy)]
pub struct LocalDef<'vir> {
    pub local: vir::LocalDeclRef<'vir>,
    pub local_snap: vir::LocalDeclSnap<'vir>,
    pub local_ex: vir::ExprRef<'vir>,
    pub impure_snap: vir::ExprSnap<'vir>,
    pub impure_pred: vir::ExprBool<'vir>,
    pub rust_ty: ty::Ty<'vir>,
}

impl TaskEncoder for MirLocalDefEnc {
    task_encoder::encoder_cache!(MirLocalDefEnc);

    type TaskDescription<'vir> = (
        DefId,  // ID of the function
        bool,   // `true` = include non-argument locals (if available)
    );

    type OutputRef<'vir> = MirLocalDefEncOutputRef;
    type OutputFullDependency<'vir> = MirLocalDefEncOutput<'vir>;

    type EncodingError = MirLocalDefEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let (def_id, all_locals) = *task_key;

        fn mk_local_def<'vir>(
            vcx: &'vir vir::VirCtxt<'vir>,
            local: mir::Local,
            ty: TyUseImpure<'vir>,
            rust_ty: ty::Ty<'vir>,
        ) -> LocalDef<'vir> {
            let ref_local = vir::vir_format!(vcx, "_{}p", local.index());
            let snap_local = vir::vir_format!(vcx, "_{}s", local.index());
            let local = vcx.mk_local_decl(ref_local, vir::TYPE_REF);
            let local_snap = vcx.mk_local_decl(snap_local, ty.snapshot());
            let local_ex = vcx.mk_local_ex(local);
            let impure_snap = ty.ref_to_snap(local_ex);
            let impure_pred = ty.ref_to_pred(vcx, local_ex, None);
            LocalDef {
                local,
                local_snap,
                local_ex,
                impure_snap,
                impure_pred,
                rust_ty,
            }
        }

        let trusted = crate::encoders::spec::is_function_trusted(def_id);
        vir::with_vcx(|vcx| {
            // TODO: refactor this a bit: split into one encoder for arguments (only)
            //   and one for locals (only)
            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let data = if !trusted
                && let Some(local_def_id) = def_id.as_local()
                && is_function_with_body(vcx.tcx(), def_id)
            {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, None);
                deps.emit_output_ref(*task_key, MirLocalDefEncOutputRef {
                    arg_count: body.arg_count,
                })?;
                let locals = IndexVec::from_fn_n(
                    |local: mir::Local| {
                        let rust_ty = body.local_decls[local].ty;
                        let rust_ty_task = RustTyDecomposition::from_ty(rust_ty, def_id);
                        let ty = deps
                            .require_dep::<TyUseImpureEnc>(rust_ty_task)
                            .unwrap();
                        mk_local_def(vcx, local, ty, rust_ty)
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
                    ty::TypingEnv::post_analysis(vcx.tcx(), def_id);
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
                    .map(|local: mir::Local| {
                        let rust_ty = if local == mir::RETURN_PLACE {
                            sig.output()
                        } else {
                            sig.inputs()[local.index() - 1]
                        };
                        let rust_ty_task = RustTyDecomposition::from_ty(rust_ty, def_id);
                        let ty = deps.require_dep::<TyUseImpureEnc>(rust_ty_task)?;
                        Ok(mk_local_def(vcx, local, ty, rust_ty))
                    })
                    .collect::<Result<IndexVec<_, _>, _>>()?;

                MirLocalDefEncOutput {
                    locals: vcx.alloc(locals),
                    arg_count: sig.inputs().len(),
                }
            };
            Ok(((), data))
        })
    }
}

impl<'vir> Index<mir::Local> for MirLocalDefEncOutput<'vir> {
    type Output = LocalDef<'vir>;
    fn index(&self, index: mir::Local) -> &Self::Output {
        &self.locals[index]
    }
}
