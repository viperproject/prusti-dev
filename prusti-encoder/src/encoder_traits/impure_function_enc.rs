use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity, ViperIdent};

use crate::encoders::{
    lifted::func_def_ty_params::LiftedTyParamsEnc, ImpureEncVisitor, MirImpureEnc, MirLocalDefEnc, MirSpecEnc
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncError;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutputRef<'vir> {
    pub method_ref: MethodIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for ImpureFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutput<'vir> {
    pub method: vir::Method<'vir>,
}

const ENCODE_REACH_BB: bool = false;

pub trait ImpureFunctionEnc
where
    Self: 'static
        + Sized
        + FunctionEnc
        + for<'vir> TaskEncoder<OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>>,
{
    /// Generates the identifier for the method; for a monomorphic encoding,
    /// this should be a name including (mangled) type arguments
    fn mk_method_ident<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        task_key: &Self::TaskKey<'vir>,
    ) -> ViperIdent<'vir>;

    fn encode<'vir>(
        task_key: Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> Result<
        ImpureFunctionEncOutput<'vir>,
        EncodeFullError<'vir, Self>,
    > {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;
            let substs = Self::get_substs(vcx, &task_key);
            let local_defs = deps
                .require_local::<MirLocalDefEnc>((def_id, substs, caller_def_id))?;

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters
            let arg_count = local_defs.arg_count + 1;

            let method_name = Self::mk_method_ident(vcx, &task_key);
            let mut args = vec![&vir::TypeData::Ref; arg_count];
            let param_ty_decls = deps
                .require_local::<LiftedTyParamsEnc>(substs)?
                .iter()
                .map(|g| g.decl())
                .collect::<Vec<_>>();
            args.extend(param_ty_decls.iter().map(|decl| decl.ty));
            let args = UnknownArity::new(vcx.alloc_slice(&args));
            let method_ref = MethodIdent::new(method_name, args);
            deps.emit_output_ref(task_key, ImpureFunctionEncOutputRef { method_ref })?;

            // Do not encode the method body if it is external, trusted or just
            // a call stub.
            let local_def_id = def_id.as_local().filter(|_| !trusted);
            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                // let body = vcx.tcx().mir_promoted(local_def_id).0.borrow();

                let fpcs_analysis = mir_state_analysis::run_free_pcs(&body, vcx.tcx());

                //let ssa_analysis = SsaAnalysis::analyse(&body);

                let block_count = body.basic_blocks.len();

                // Local count for the Viper method:
                // - one for each basic block;
                // - one (`Ref`) for each non-argument, non-return local.
                let _local_count = block_count + 1 * (body.local_decls.len() - arg_count);

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    let name_p = local_defs.locals[local].local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None),
                    )
                }
                if ENCODE_REACH_BB {
                    start_stmts.extend((0..block_count).map(|block| {
                        let name = vir::vir_format!(vcx, "_reach_bb{block}");
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [name] : Bool },
                            Some(vcx.mk_todo_expr("false")),
                        )
                    }));
                }
                encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::Start),
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0))),
                ));

                let mut visitor = ImpureEncVisitor {
                    monomorphize: MirImpureEnc::monomorphize(),
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    //ssa_analysis,
                    fpcs_analysis,
                    local_defs,

                    tmp_ctr: 0,

                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(&body);

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    &[],
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));
                Some(vcx.alloc_slice(&visitor.encoded_blocks))
            } else {
                None
            };

            let spec = deps
                .require_local::<MirSpecEnc>((def_id, substs, None, false))?;
            let (spec_pres, spec_posts) = (spec.pres, spec.posts);

            let mut pres = Vec::with_capacity(arg_count - 1);
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 0..arg_count {
                let name_p = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != 0 {
                    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                }
            }
            args.extend(param_ty_decls.iter());
            pres.extend(spec_pres);

            let mut posts = Vec::with_capacity(spec_posts.len() + 1);
            posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);
            posts.extend(spec_posts);

            Ok(ImpureFunctionEncOutput {
                method: vcx.mk_method(
                    method_ref,
                    vcx.alloc_slice(&args),
                    &[],
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks,
                ),
            })
        })
    }
}
