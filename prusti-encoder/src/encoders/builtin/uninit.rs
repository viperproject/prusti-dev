use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::PredicateIdn;

/// The token predicate `Uninit(self, t)` for a place of (lifted) type `t` at
/// address `self` whose storage is allocated but which holds no value: the
/// place is either freshly `StorageLive`, was moved out of, or was dropped.
/// The `assign` method of every type consumes the token in exchange for the
/// type's owned predicate, so a place can never receive an owned predicate it
/// (or its enclosing scope) does not have room for. The token is abstract; it
/// is parameterised by the lifted type value rather than being a per-type
/// predicate so that no generic casts are needed at call boundaries.
pub struct UninitEnc;

impl TaskEncoder for UninitEnc {
    task_encoder::encoder_cache!(UninitEnc);
    const ENCODER_NAME: &'static str = "uninitialised token encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = PredicateIdn<'vir, (vir::Ref, vir::TyVal)>;
    type OutputFullLocal<'vir> = vir::Predicate<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let idn = PredicateIdn::new(
            vir::ViperIdent::new("Uninit"),
            (vir::TYPE_REF, vir::TYPE_TYVAL),
        );
        vir::with_vcx(|vcx| {
            let self_decl = vcx.mk_local_decl("self", vir::TYPE_REF);
            let ty_decl = vcx.mk_local_decl("t", vir::TYPE_TYVAL);
            let predicate = vcx.mk_predicate(idn, (self_decl, ty_decl), None);
            Ok((predicate, idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        match Self::all_outputs_local_no_errors(program).as_slice() {
            [] => (),
            [predicate] => program.add_predicate(predicate),
            _ => unreachable!(),
        }
    }
}
