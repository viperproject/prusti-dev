use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::FunctionIdn;

use crate::encoders::{
    builtin::{
        MetadataCastAxiomEnc, ValueCastAxiomEnc,
        cast::{MirBuiltinCastEnc, MirBuiltinCastOutput, MirBuiltinCastTask},
    },
    ty::{
        RustTyDecomposition, RustTySpecial, TySpecifics,
        generics::{GArgsTy, GArgsTyEnc},
    },
};

/// See `MirBuiltinCastEnc`. This adds a wrapper which substitutes in the
/// concrete type arguments.
pub struct MirBuiltinUseCastEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MirBuiltinUseCastTask<'vir> {
    result_ty: RustTyDecomposition<'vir>,
    kind: mir::CastKind,
    operand_ty: RustTyDecomposition<'vir>,
}

impl<'vir> MirBuiltinUseCastTask<'vir> {
    pub fn new(
        result_ty: RustTyDecomposition<'vir>,
        kind: mir::CastKind,
        operand_ty: RustTyDecomposition<'vir>,
    ) -> Self {
        // Canonicalize away the `CoercionSource`: whether a coercion was
        // written as an explicit `as` cast or inserted implicitly does not
        // affect the encoding, but as part of the task key it would create two
        // tasks emitting the same Viper function (a duplicate-identifier
        // consistency error).
        let kind = match kind {
            mir::CastKind::PointerCoercion(coercion, _) => {
                mir::CastKind::PointerCoercion(coercion, mir::CoercionSource::Implicit)
            }
            other => other,
        };
        Self {
            result_ty,
            kind,
            operand_ty,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum MirBuiltinUseCastOutput<'vir> {
    Simple(FunctionIdn<'vir, vir::CSnap, vir::CSnap>),
    Unsize(MirBuiltinUnsize<'vir>),
}

#[derive(Debug, Copy, Clone)]
pub struct MirBuiltinUnsize<'vir> {
    cast: FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap), vir::CSnap>,
    unsize: Option<vir::MethodIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap)>>,
    undo: Option<vir::MethodIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap)>>,
    /// The operand and result referent type values `[U, V]`, used by the `cast`
    /// function (to construct the metadata) and by the `unsize`/`undo` methods (to
    /// transfer the referent's `p_Param` predicate and value).
    generics: GArgsTy<'vir>,
}

impl<'vir> MirBuiltinUseCastOutput<'vir> {
    pub fn cast<Curr, Next>(
        &self,
        input: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenCSnap<'vir, Curr, Next> {
        match self {
            MirBuiltinUseCastOutput::Simple(f) => f.call()(input),
            MirBuiltinUseCastOutput::Unsize(u) => {
                u.cast.call()(input, u.generics.get_ty(), u.generics.get_const())
            }
        }
    }

    pub fn unsize<Curr, Next>(
        &self,
        input: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> Option<vir::StmtGen<'vir, Curr, Next>> {
        match self {
            MirBuiltinUseCastOutput::Simple(..) => None,
            MirBuiltinUseCastOutput::Unsize(u) => u
                .unsize
                .map(|f| f.call()(input, u.generics.get_ty(), u.generics.get_const()))
                .map(vir::StmtKindGenData::alloc),
        }
    }

    pub fn undo<Curr, Next>(
        &self,
        input: vir::ExprGenCSnap<'vir, Curr, Next>,
    ) -> Option<vir::StmtGen<'vir, Curr, Next>> {
        match self {
            MirBuiltinUseCastOutput::Simple(..) => None,
            MirBuiltinUseCastOutput::Unsize(u) => u
                .undo
                .map(|f| f.call()(input, u.generics.get_ty(), u.generics.get_const()))
                .map(vir::StmtKindGenData::alloc),
        }
    }
}

impl TaskEncoder for MirBuiltinUseCastEnc {
    task_encoder::encoder_cache!(MirBuiltinUseCastEnc);
    const ENCODER_NAME: &'static str = "MIR builtin use cast encoder";

    type TaskDescription<'vir> = MirBuiltinUseCastTask<'vir>;

    type OutputFullDependency<'vir> = MirBuiltinUseCastOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let MirBuiltinUseCastTask {
            result_ty,
            kind,
            operand_ty,
        } = *task_key;
        let task = MirBuiltinCastTask {
            result_ty: result_ty.ty,
            kind,
            operand_ty: operand_ty.ty,
        };
        let cast = deps.require_dep::<MirBuiltinCastEnc>(task)?;
        match cast {
            MirBuiltinCastOutput::Simple(fn_idn) => {
                Ok(((), MirBuiltinUseCastOutput::Simple(fn_idn)))
            }
            MirBuiltinCastOutput::Unsize { cast, undo, unsize } => {
                // The cast function and the unsize/undo methods are all generic over
                // the operand and result referent type values `[U, V]`. The referent
                // is now index 0 of each reference's type args (the metadata type is
                // derived from the referent, and the lifetime is not a type arg).
                let op_generics = deps.require_dep::<GArgsTyEnc>(operand_ty.args)?;
                let result_generics = deps.require_dep::<GArgsTyEnc>(result_ty.args)?;
                let generics = vir::with_vcx(|vcx| {
                    GArgsTy::new(
                        vcx.alloc_slice(&[op_generics.get_ty()[0], result_generics.get_ty()[0]]),
                        &[],
                    )
                });
                let unsize = MirBuiltinUnsize {
                    cast,
                    unsize,
                    undo,
                    generics,
                };
                // Recover the operand/result referent (`[T; N]` / `[T]`) structure by
                // normalizing the reference's (generic `p_Param`) referent type
                // against the reference's args.
                let (op_ref, res_ref) = match (&operand_ty.ty.specifics, &result_ty.ty.specifics) {
                    (TySpecifics::ImmRef(od), TySpecifics::ImmRef(rd)) => {
                        (od.referent, rd.referent)
                    }
                    (TySpecifics::MutRef(od), TySpecifics::MutRef(rd)) => {
                        (od.referent, rd.referent)
                    }
                    (TySpecifics::Raw(od), TySpecifics::Raw(rd)) => (od.referent, rd.referent),
                    // A `Box` unsize coercion: the referent is the boxed value.
                    (TySpecifics::StructLike(_), TySpecifics::StructLike(_))
                        if operand_ty.ty.special == RustTySpecial::Box =>
                    {
                        (operand_ty.ty.box_value_ty(), result_ty.ty.box_value_ty())
                    }
                    // `MirBuiltinCastOutput::Unsize` should only happen for
                    // reference/pointer types, do not expect other types here.
                    _ => unreachable!(
                        "unexpected operand/result reference types for pointer cast: {operand_ty:?} / {result_ty:?}"
                    ),
                };
                let op_inner = op_ref.decompose_normalize(operand_ty.args);
                let res_inner = res_ref.decompose_normalize(result_ty.args);
                deps.require_dep::<MetadataCastAxiomEnc>((op_inner.ty, res_inner.ty))?;
                deps.require_dep::<ValueCastAxiomEnc>((op_inner.ty, res_inner.ty))?;
                Ok(((), MirBuiltinUseCastOutput::Unsize(unsize)))
            }
        }
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        MirBuiltinCastEnc::emit_outputs(program);
    }
}
