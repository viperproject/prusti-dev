use task_encoder::TaskEncoder;
use vir::{Function, FunctionIdn, ViperIdent};

/// Encodes the `Int` to `Ref` function to construct a reference from an address. In
/// the future this will also likely include a second `Int` tag argument
/// (from SB or TB) and inverse functions for both.
pub struct RefDataEnc;

#[derive(Debug, Clone)]
pub struct RefData<'vir> {
    pub addr_to_ref: vir::FunctionIdn<'vir, vir::Int, vir::Ref>,
}

#[derive(Debug, Clone)]
pub struct RefDataLocal<'vir> {
    addr_to_ref_fn: Function<'vir>,
}

impl TaskEncoder for RefDataEnc {
    task_encoder::encoder_cache!(RefDataEnc);
    const ENCODER_NAME: &'static str = "ref data encoder";
    type TaskDescription<'vir> = ();
    type OutputFullLocal<'vir> = RefDataLocal<'vir>;
    type OutputFullDependency<'vir> = RefData<'vir>;

    type TaskKey<'vir> = Self::TaskDescription<'vir>;

    fn task_to_key<'vir>(_task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {}

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let addr_to_ref =
            FunctionIdn::new(ViperIdent::new("addr_to_ref"), vir::TYPE_INT, vir::TYPE_REF);
        let addr_to_ref_fn = vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_INT);
            vcx.mk_function(addr_to_ref, (arg_decl,), &[], &[], None, None)
        });
        Ok((RefDataLocal { addr_to_ref_fn }, RefData { addr_to_ref }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = RefDataEnc::all_outputs_local_no_errors();
        for output in outputs {
            program.add_function(output.addr_to_ref_fn);
        }
    }
}
