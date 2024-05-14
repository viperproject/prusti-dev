use task_encoder::{TaskEncoder, TaskEncoderDependencies, EncodeFullResult};

use super::{domain::{DomainEnc, DomainEncSpecifics}, lifted::generic::{LiftedGeneric, LiftedGenericEnc}, most_generic_ty::MostGenericTy};

/// Takes a Rust `Ty` and returns a Viper `Type`. The returned type is always a
/// domain type. To get specifics such as constructors for the domain, use the
/// full encoding: this is generally the one to use as it also includes the type.
pub struct SnapshotEnc;

#[derive(Clone, Debug)]
pub struct SnapshotEncOutputRef<'vir> {
    pub snapshot: vir::Type<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for SnapshotEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct SnapshotEncOutput<'vir> {
    pub base_name: String,
    pub snapshot: vir::Type<'vir>,
    pub generics: &'vir [LiftedGeneric<'vir>],
    pub specifics: DomainEncSpecifics<'vir>,
}

impl TaskEncoder for SnapshotEnc {
    task_encoder::encoder_cache!(SnapshotEnc);

    type TaskDescription<'tcx> = MostGenericTy<'tcx>;
    type OutputRef<'vir> = SnapshotEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = SnapshotEncOutput<'vir>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        ty: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let out = deps.require_ref::<DomainEnc>(*ty)?;
            let snapshot = out.domain.apply(vcx, []);
            deps.emit_output_ref(
                *ty,
                SnapshotEncOutputRef {
                    snapshot,
                },
            )?;
            let specifics = deps.require_dep::<DomainEnc>(*ty)?;
            let generics = vcx.alloc_slice(
                &ty.generics()
                    .into_iter()
                    .map(|g| deps.require_ref::<LiftedGenericEnc>(*g).unwrap())
                    .collect::<Vec<_>>()
            );
            Ok((
                SnapshotEncOutput {
                    base_name: out.base_name,
                    snapshot,
                    specifics,
                    generics,
                },
                (),
            ))
        })
    }
}
