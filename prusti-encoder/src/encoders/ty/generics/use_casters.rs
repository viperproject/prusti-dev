use std::marker::PhantomData;

use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{Impure, Pure, Purity, ty::RustTyNormalized};

use super::{
    GArgsTy, GArgsTyEnc,
    casters::{CastersEnc, GArgCasters, PurityCasters},
};

pub struct GArgsCastEnc<P: Purity>(PhantomData<P>);

/// One specific caster (if any).
#[derive(Debug, Clone, Copy)]
pub enum GArgCaster<'vir, P: PurityCasters> {
    Casters(Casters<'vir, P>),
    /// Either the type was already concrete or the param type remained as a
    /// param after normalization.
    NoCast,
}

#[derive(Debug, Clone, Copy)]
pub struct Casters<'vir, P: PurityCasters> {
    cast: GArgCasters<'vir, P>,
    ty_args: GArgsTy<'vir>,
}

impl<'vir, P: PurityCasters> GArgCaster<'vir, P> {
    fn get(self) -> Option<Casters<'vir, P>> {
        match self {
            GArgCaster::Casters(casters) => Some(casters),
            GArgCaster::NoCast => None,
        }
    }
}

// utility functions to allow doing `ty_casters[gidx].cast_to_...`

impl<'vir> GArgCaster<'vir, Pure> {
    pub fn cast_to_callee_ctx<Curr, Next>(
        &self,
        e: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.get()
            .map(|c| {
                c.cast.make_generic.call()(
                    e.downcast_ty(),
                    c.ty_args.get_ty(),
                    c.ty_args.get_const(),
                )
                .upcast_ty()
            })
            .unwrap_or(e)
    }

    pub fn cast_to_caller_ctx<Curr, Next>(
        &self,
        e: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.get()
            .map(|c| c.cast.make_concrete.call()(e.downcast_ty()).upcast_ty())
            .unwrap_or(e)
    }
}

impl<'vir> GArgCaster<'vir, Impure> {
    pub fn cast_to_callee_ctx(&self, e: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.get()
            .map(|c| (c.cast.make_generic)(e, c.ty_args.get_ty(), c.ty_args.get_const()).alloc())
    }

    pub fn cast_to_caller_ctx(&self, e: vir::ExprRef<'vir>) -> Option<vir::Stmt<'vir>> {
        self.get()
            .map(|c| (c.cast.make_concrete)(e, c.ty_args.get_ty(), c.ty_args.get_const()).alloc())
    }
}

impl TaskEncoder for GArgsCastEnc<Pure> {
    task_encoder::encoder_cache!(GArgsCastEnc<Pure>);
    const ENCODER_NAME: &'static str = "pure generic args cast encoder";
    type TaskDescription<'tcx> = Option<RustTyNormalized<'tcx>>;
    type OutputFullDependency<'vir> = GArgCaster<'vir, Pure>;
    type OutputFullLocal<'vir> = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let Some(ty) = task_key else {
            return Ok(((), GArgCaster::NoCast));
        };

        let cast = deps.require_ref::<CastersEnc<Pure>>((ty.param, ty.concrete.ty))?;
        let ty_args = deps.require_dep::<GArgsTyEnc>(ty.concrete.args)?;
        Ok(((), GArgCaster::Casters(Casters { cast, ty_args })))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        CastersEnc::<Pure>::emit_outputs(program);
    }
}

impl TaskEncoder for GArgsCastEnc<Impure> {
    task_encoder::encoder_cache!(GArgsCastEnc<Impure>);
    const ENCODER_NAME: &'static str = "impure generic args cast encoder";
    type TaskDescription<'tcx> = Option<RustTyNormalized<'tcx>>;
    type OutputFullDependency<'vir> = GArgCaster<'vir, Impure>;
    type OutputFullLocal<'vir> = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let Some(ty) = task_key else {
            return Ok(((), GArgCaster::NoCast));
        };
        let cast = deps.require_ref::<CastersEnc<Impure>>((ty.param, ty.concrete.ty))?;
        let ty_args = deps.require_dep::<GArgsTyEnc>(ty.concrete.args)?;
        Ok(((), GArgCaster::Casters(Casters { cast, ty_args })))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        CastersEnc::<Impure>::emit_outputs(program);
    }
}
