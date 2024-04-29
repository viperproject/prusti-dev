use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::with_vcx;

use crate::encoders::SnapshotEnc;

use super::{most_generic_ty::extract_type_params, snapshot::{SnapshotEncOutput, SnapshotEncOutputRef}};

pub struct RustTySnapshotsEnc;

#[derive(Clone)]
pub struct RustTySnapshotsEncOutputRef<'vir> {
    pub generic_snapshot: SnapshotEncOutputRef<'vir>,
}

#[derive(Clone)]
pub struct RustTySnapshotsEncOutput<'vir> {
    pub generic_snapshot: SnapshotEncOutput<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for RustTySnapshotsEncOutputRef<'vir> {}

impl TaskEncoder for RustTySnapshotsEnc {
    task_encoder::encoder_cache!(RustTySnapshotsEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = RustTySnapshotsEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = RustTySnapshotsEncOutput<'vir>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
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
        with_vcx(|vcx| {
            let (generic_ty, args) = extract_type_params(vcx.tcx(), *task_key);
            let generic_snapshot = deps.require_ref::<SnapshotEnc>(generic_ty).unwrap();
            deps.emit_output_ref::<RustTySnapshotsEnc>(
                *task_key,
                RustTySnapshotsEncOutputRef { generic_snapshot },
            );
            for arg in args {
                deps.require_ref::<RustTySnapshotsEnc>(arg).unwrap();
            }
            let generic_snapshot = deps
                .require_local::<SnapshotEnc>(generic_ty)
                .unwrap();
            Ok((RustTySnapshotsEncOutput { generic_snapshot }, ()))
        })
    }
}
