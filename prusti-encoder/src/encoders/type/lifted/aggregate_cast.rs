use prusti_rustc_interface::{
    abi::VariantIdx,
    middle::{mir, ty::{GenericArgs, Ty}},
    span::def_id::DefId,
};
use task_encoder::TaskEncoder;

use crate::encoders::lifted::cast::{CastArgs, CastToEnc};

use super::{cast::PureCast, casters::CastTypePure, rust_ty_cast::RustTyCastersEnc};

/// Casts arguments to the snapshot constructor for an aggregate type (e.g.
/// Tuples, ADTs) to appropriate (generic or concrete) Viper representations,
/// depending on what the aggregate constructor expects.
pub struct AggregateSnapArgsCastEnc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AggregateSnapArgsCastEncTask<'tcx> {
    pub tys: Vec<Ty<'tcx>>,
    pub aggregate_type: AggregateType,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AggregateType {
    Tuple,
    Adt {
        def_id: DefId,
        variant_index: VariantIdx,
    },
}

impl From<&mir::AggregateKind<'_>> for AggregateType {
    fn from(aggregate_kind: &mir::AggregateKind) -> Self {
        match aggregate_kind {
            mir::AggregateKind::Tuple => Self::Tuple,
            mir::AggregateKind::Adt(def_id, variant_index, ..) => {
                Self::Adt {
                    def_id: *def_id,
                    variant_index: *variant_index,
                }
            }
            _ => unimplemented!(),
        }
    }
}

#[derive(Clone)]
pub struct AggregateSnapArgsCastEncOutput<'vir>(
    &'vir [Option<PureCast<'vir>>],
);

impl<'vir> AggregateSnapArgsCastEncOutput<'vir> {
    pub fn apply_casts<Curr, Next>(
        &self,
        vcx: &'vir vir::VirCtxt<'_>,
        exprs: impl Iterator<Item = vir::ExprGen<'vir, Curr, Next>>,
    ) -> Vec<vir::ExprGen<'vir, Curr, Next>> {
        self.0
            .iter()
            .zip(exprs)
            .map(|(cast, expr)| match cast {
                Some(cast) => cast.apply(vcx, expr),
                None => expr,
            })
            .collect()
    }
}

impl TaskEncoder for AggregateSnapArgsCastEnc {
    task_encoder::encoder_cache!(AggregateSnapArgsCastEnc);

    type TaskDescription<'tcx> = AggregateSnapArgsCastEncTask<'tcx>;

    type OutputFullLocal<'vir> = AggregateSnapArgsCastEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'tcx>(task: &Self::TaskDescription<'tcx>) -> Self::TaskKey<'tcx> {
        task.clone()
    }

    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        deps.emit_output_ref::<AggregateSnapArgsCastEnc>(task_key.clone(), ());
        vir::with_vcx(|vcx| {
            let cast_functions: Vec<Option<PureCast<'vir>>> =
                match task_key.aggregate_type {
                    AggregateType::Tuple => task_key
                        .tys
                        .iter()
                        .map(|ty| {
                            let cast_functions =
                                deps.require_local::<RustTyCastersEnc<CastTypePure>>(*ty).unwrap();
                            cast_functions.to_generic_cast().map(|c| c.map_applicator(|f| f.as_unknown_arity()))
                        })
                        .collect::<Vec<_>>(),
                    AggregateType::Adt {
                        def_id,
                        variant_index,
                    } => {
                        let adt_def = vcx.tcx().adt_def(def_id);
                        let variant = &adt_def.variant(variant_index);
                        assert!(variant.fields.len() == task_key.tys.len());
                        let identity_substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
                        variant
                            .fields
                            .iter()
                            .zip(task_key.tys.iter())
                            .map(|(v_field, actual_ty)| {
                                let cast = deps
                                    .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                                        expected: v_field.ty(vcx.tcx(), identity_substs),
                                        actual: *actual_ty,
                                    })
                                    .unwrap();
                                cast.cast_function()
                            })
                            .collect::<Vec<_>>()
                    }
                };
            Ok((
                AggregateSnapArgsCastEncOutput(vcx.alloc(cast_functions)),
                (),
            ))
        })
    }
}
