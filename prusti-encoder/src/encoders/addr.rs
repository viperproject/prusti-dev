use task_encoder::TaskEncoder;
use vir::{Function, FunctionIdn, ViperIdent};

/// Encodes the `Int` to `Ref` function to construct a reference from an address. In
/// the future this will also likely include a second `Int` tag argument
/// (from SB or TB) and inverse functions for both.
pub struct RefDataEnc;

#[derive(Debug, Clone)]
pub struct RefData<'vir> {
    // The second parameter is the Ref of the higher-level structure (for example the struct for a field) acting like the tag of that ref - we call this the base ref
    pub addr_to_ref: vir::FunctionIdn<'vir, (vir::Int, vir::Ref), vir::Ref>,
    pub ref_to_addr: vir::FunctionIdn<'vir, vir::Ref, vir::Int>,
    pub base_ref: vir::FunctionIdn<'vir, vir::Ref, vir::Ref>,
    pub parent_ref: vir::FunctionIdn<'vir, vir::Ref, vir::Ref>,
    pub offset: vir::FunctionIdn<'vir, (vir::TyVal, vir::Int), vir::Int>,
}

#[derive(Debug, Clone)]
pub struct RefDataLocal<'vir> {
    addr_to_ref_fn: Function<'vir>,
    ref_to_addr_fn: Function<'vir>,
    base_ref_fn: Function<'vir>,
    parent_ref_fn: Function<'vir>,
    offset_fn: Function<'vir>,
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
        let addr_to_ref = FunctionIdn::new(
            ViperIdent::new("addr_to_ref"),
            (vir::TYPE_INT, vir::TYPE_REF),
            vir::TYPE_REF,
        );
        let addr_to_ref_fn = vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_INT);
            let base_decl = vcx.mk_local_decl("base", vir::TYPE_REF);
            vcx.mk_function(addr_to_ref, (arg_decl, base_decl), &[], &[], None, None)
        });
        let ref_to_addr =
            FunctionIdn::new(ViperIdent::new("ref_to_addr"), vir::TYPE_REF, vir::TYPE_INT);
        let ref_to_addr_fn = vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_REF);
            vcx.mk_function(ref_to_addr, (arg_decl,), &[], &[], None, None)
        });
        let base_ref = FunctionIdn::new(ViperIdent::new("base_ref"), vir::TYPE_REF, vir::TYPE_REF);
        let base_ref_fn = vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_REF);
            vcx.mk_function(base_ref, (arg_decl,), &[], &[], None, None)
        });
        let parent_ref =
            FunctionIdn::new(ViperIdent::new("parent_ref"), vir::TYPE_REF, vir::TYPE_REF);
        let parent_ref_fn = vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", vir::TYPE_REF);
            vcx.mk_function(parent_ref, (arg_decl,), &[], &[], None, None)
        });
        let offset = FunctionIdn::new(
            ViperIdent::new("offset"),
            (vir::TYPE_TYVAL, vir::TYPE_INT),
            vir::TYPE_INT,
        );
        let offset_fn = vir::with_vcx(|vcx| {
            let ty_decl = vcx.mk_local_decl("ty", vir::TYPE_TYVAL);
            let field_idx_decl = vcx.mk_local_decl("field_idx", vir::TYPE_INT);
            vcx.mk_function(offset, (ty_decl, field_idx_decl), &[], &[], None, None)
        });
        Ok((
            RefDataLocal {
                addr_to_ref_fn,
                ref_to_addr_fn,
                base_ref_fn,
                parent_ref_fn,
                offset_fn,
            },
            RefData {
                addr_to_ref,
                ref_to_addr,
                base_ref,
                parent_ref,
                offset,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = RefDataEnc::all_outputs_local_no_errors();
        for output in outputs {
            program.add_function(output.addr_to_ref_fn);
            program.add_function(output.ref_to_addr_fn);
            program.add_function(output.base_ref_fn);
            program.add_function(output.parent_ref_fn);
            program.add_function(output.offset_fn);
        }
    }
}
