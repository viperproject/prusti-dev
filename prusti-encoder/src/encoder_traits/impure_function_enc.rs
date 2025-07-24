use std::alloc::Global;

use pcg::{borrow_checker::r#impl::BorrowCheckerImpl, r#loop::LoopAnalysis};
use prusti_rustc_interface::middle::mir;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdn, ViperIdent};

use crate::{
    encoders::{
        lifted::func_def_ty_params::LiftedTyParamsEnc, ImpureEncVisitor, MirImpureEnc,
        MirLocalDefEnc, MirSpecEnc, WandEnc, WandEncTask,
    },
    trait_support::is_function_with_body,
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncError;

#[derive(Clone, Debug)]
pub struct ImpureFunctionEncOutputRef<'vir> {
    pub method_ref: MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal)>,
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
    ) -> Result<ImpureFunctionEncOutput<'vir>, EncodeFullError<'vir, Self>> {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;

            let substs = Self::get_substs(vcx, &task_key);
            let trusted = crate::encoders::is_function_trusted(def_id, substs);

            let local_defs =
                deps.require_local::<MirLocalDefEnc>((def_id, substs, caller_def_id))?;

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters: for generic methods we will want to pass
            //   values of type `Type` as well`
            let arg_count = local_defs.arg_count + 1;

            // Create the identifier and use it as an output ref. This is what
            // is used when other methods call this one.
            let method_name = Self::mk_method_ident(vcx, &task_key);
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
            let param_ty_decls = deps
                .require_local::<LiftedTyParamsEnc>(substs)?
                .iter()
                .map(|g| g.decl())
                .collect::<Vec<_>>();
            let ty_args = vcx.alloc_slice(
                &param_ty_decls
                    .iter()
                    .map(|decl| decl.ty)
                    .collect::<Vec<_>>(),
            );
            let method_ref = MethodIdn::new(method_name, (ref_args, ty_args));
            deps.emit_output_ref(task_key, ImpureFunctionEncOutputRef { method_ref })?;

            // Method contract. We will need to emit pre- and postconditions for
            // the permissions, the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;
            let wands = deps.require_local::<WandEnc>(WandEncTask { def_id })?;

            // Add direct resources for inputs and outputs to the pre- and
            // postconditions, respectively. "Direct" here refers to owned
            // Viper resources that must be passed in/out given the signature,
            // without going through any dereferences.
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 0..arg_count {
                let name_p = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != 0 {
                    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                }
            }
            posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);

            // ..
            pres.extend(wands.indirect_pres(vcx, &local_defs, deps));
            posts.extend(wands.indirect_posts(vcx, &local_defs, deps));
            posts.extend(wands.wand_posts(vcx, &local_defs, deps));

            // Do not encode the method body if it is external, trusted, just
            // a call stub, or a trait function without a default implementation
            let local_def_id = def_id
                .as_local()
                .filter(|_| !trusted && is_function_with_body(vcx.tcx(), def_id));
            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                let body_with_facts = vcx.body_mut().get_impure_fn_body_with_facts(local_def_id);

                let loop_analysis = LoopAnalysis::find_loops(&body);
                let bc = BorrowCheckerImpl::new(vcx.tcx(), &body_with_facts);
                let pcg_ctxt = pcg::PcgCtxt::new(&body_with_facts.body, vcx.tcx(), &bc);
                let fpcs_analysis = pcg::run_pcg(&pcg_ctxt, Global, None);

                let block_count = body.basic_blocks.len();

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
                            Some(vcx.mk_bool::<false>()),
                        )
                    }));
                }
                // This will be overwritten later.
                encoded_blocks.push(vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    &[],
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                ));

                deps.check_cycle()?;
                let mut visitor = ImpureEncVisitor {
                    monomorphize: MirImpureEnc::monomorphize(),
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    body: &body,

                    loop_analysis,
                    wands,

                    tmp_ctr: 0,
                    label_ctr: 0,
                    call_labels: Default::default(),
                    from_to_vars: Default::default(),

                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                visitor.visit_body(&body);
                start_stmts.extend(visitor.from_to_vars.iter().flat_map(|(_, v)| v.iter()).map(
                    |(_, v)| {
                        vcx.mk_local_decl_stmt(
                            vir::vir_local_decl! { vcx; [v] : Bool },
                            Some(vcx.mk_bool::<false>()),
                        )
                    },
                ));
                visitor.encoded_blocks[0] = vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                );

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    &[],
                    &[],
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));

                visitor.deps.check_cycle()?;

                Some(visitor.encoded_blocks)
            } else {
                None
            };

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres);
            posts.extend(spec.posts);

            Ok(ImpureFunctionEncOutput {
                method: vcx.mk_method(
                    method_ref,
                    (&args, &param_ty_decls),
                    &[],
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                ),
            })
        })
    }
}
