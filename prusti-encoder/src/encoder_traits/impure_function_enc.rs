use std::collections::{HashMap, HashSet};

use pcs::borrow_pcg::unblock_graph::UnblockGraph;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    middle::{mir, ty::{self, GenericArgs}},
    span::Span,
};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{MethodIdent, UnknownArity, ViperIdent};

use crate::encoders::{
    indirect::IndirectPredicatesEnc, lifted::func_def_ty_params::LiftedTyParamsEnc, rust_ty_predicates::RustTyPredicatesEnc, EncodedWand, ImpureEncVisitor, MirImpureEnc, MirLocalDefEnc, MirSpecEnc, WandEnc, WandEncTask
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
    ) -> Result<ImpureFunctionEncOutput<'vir>, EncodeFullError<'vir, Self>> {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();
        vir::with_vcx(|vcx| {
            use mir::visit::Visitor;
            use vir::Reify;

            let tcx = vcx.tcx();
            let substs = Self::get_substs(vcx, &task_key);
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

            // Method contract. We will need to emit pre- and postconditions for
            // the permissions, the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;
            let wands = deps.require_local::<WandEnc>(WandEncTask {
                def_id,
                substs,
            })?;

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
            let wands = wands.reify(vcx, (def_id, vcx.alloc_slice(&(0..arg_count)
                .map(|arg_idx| local_defs.locals[arg_idx.into()].local_ex)
                .collect::<Vec<_>>())));

            pres.extend(wands.indirect_pres.clone());
            posts.extend(wands.indirect_posts.clone());
            /*
            posts.extend(wands.encoded_wands.iter()
                .map(|EncodedWand { wand, .. }| {
                    let mut wand_expr = vcx.mk_wand_expr(wand);
                    if let Some((expr, snap)) = output_in_wand {
                        wand_expr = vcx.mk_let_expr("_0r", expr, wand_expr);
                        wand_expr = vcx.mk_let_expr("_0s", snap, wand_expr);
                    }
                    wand_expr
                }));
            */

            // Do not encode the method body if it is external, trusted, or just
            // a call stub.
            let local_def_id = def_id.as_local().filter(|_| !trusted);
            let blocks = if let Some(local_def_id) = local_def_id {
                let body = vcx
                    .body_mut()
                    .get_impure_fn_body(local_def_id, substs, caller_def_id);
                let body_with_facts = vcx
                    .body_mut()
                    .get_impure_fn_body_with_facts(local_def_id);

                let mut fpcs_analysis = pcs::run_combined_pcs(&body_with_facts, vcx.tcx(), None);

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
                            Some(vcx.mk_todo_expr("false")),
                        )
                    }));
                }
                encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::Start),
                    vcx.alloc_slice(&start_stmts),
                    vcx.mk_goto_stmt(vcx.alloc(vir::CfgBlockLabelData::BasicBlock(0))),
                ));

                let last_block = (block_count - 1).into();
                let final_borrow_state = fpcs_analysis
                    .get_all_for_bb(last_block)
                    .unwrap()
                    .map(|block| block.statements
                        .last()
                        .unwrap()
                        .borrows
                        .post_main().clone());

                deps.check_cycle()?;
                let mut visitor = ImpureEncVisitor {
                    monomorphize: MirImpureEnc::monomorphize(),
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,

                    tmp_ctr: 0,

                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,

                    place_overrides: HashMap::new(),
                };
                visitor.visit_body(&body);

                let wand_packages = final_borrow_state
                    .map(|state| wands.package_wands(state, &mut visitor))
                    .unwrap_or_default();

                visitor.encoded_blocks.push(vcx.mk_cfg_block(
                    vcx.alloc(vir::CfgBlockLabelData::End),
                    vcx.alloc_slice(&wand_packages),
                    vcx.alloc(vir::TerminatorStmtData::Exit),
                ));

                visitor.deps.check_cycle()?;

                Some(visitor.encoded_blocks)
            } else {
                None
            };

            // in the postcondition, we need to provide permissions to:
            // - the return place
            // - referenced (aka indirect) resources that are not blocked
            // - magic wands for resources that are blocked

            // which resources are blocked?
            // - fn foo<'a>(x: &'a mut i32) -> &'a mut i32; // mutref covariant in its lifetime
            //   *x is blocked
            // - struct Foo<'a>(&'a mut i32) // Foo is covariant in 'a
            //   fn foo<'a>(x: Foo<'a>) -> &'a mut i32;
            //   *x.0 is blocked

            /*
            let identity_substs = GenericArgs::identity_for_item(vcx.tcx(), def_id);
            wands_println!("regions of {def_id:?}:");
            for region in identity_substs {
                wands_println!("  {region:?}");
            }

            wands_println!("regions of args?");
            let body = vcx
                .body_mut()
                .get_impure_fn_body_with_facts(def_id.as_local().unwrap());
            for l in 0..local_defs.locals.len() {
                let ty = body.body.local_decls[l.into()].ty;
                wands_println!("  arg: {ty:?}");
            }

            wands_println!("regions in region inference context?");
            for region in body.region_inference_context.regions() {
                wands_println!("  region: {region:?}");
            }
            */
            args.extend(param_ty_decls.iter());

            //for arg_idx in 0..arg_count {
            //    if let Some((pre, post)) = local_defs.locals[arg_idx.into()].impure_indirect_pred {
            //        posts.push(post);
            //    }
            //}

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pres);
            posts.extend(spec.posts);

            Ok(ImpureFunctionEncOutput {
                method: vcx.mk_method(
                    method_ref,
                    vcx.alloc_slice(&args),
                    &[],
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                ),
            })
        })
    }
}
