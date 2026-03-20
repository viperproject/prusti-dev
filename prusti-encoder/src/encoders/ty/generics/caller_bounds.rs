use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::ty::generics::GParams;

struct CallerBoundsEnc;

impl TaskEncoder for CallerBoundsEnc {
    task_encoder::encoder_cache!(CallerBoundsEnc);

    const ENCODER_NAME: &'static str = "caller bounds encoder";

    type TaskDescription<'vir> = GParams<'vir>;

    type OutputFullDependency<'vir> = vir::ExprBool<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        _deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
    }
}
