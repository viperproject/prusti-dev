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
    indirect::IndirectPredicatesEnc, lifted::func_def_ty_params::LiftedTyParamsEnc, rust_ty_predicates::RustTyPredicatesEnc, ImpureEncVisitor, MirImpureEnc, MirLocalDefEnc, MirSpecEnc
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
            // TODO: type parameters
            let arg_count = local_defs.arg_count + 1;

            macro_rules! wands_println {
                ($($args:tt)*) => {
                    // println!($($args)*)
                };
            }

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

            // method contract
            let mut pres = Vec::new(); // Vec::with_capacity(arg_count - 1);
            let mut posts = Vec::new(); // Vec::with_capacity(spec_posts.len() + 1);

            // direct resources for inputs and outputs
            let mut args = Vec::with_capacity(arg_count + substs.len());
            for arg_idx in 0..arg_count {
                let name_p = local_defs.locals[arg_idx.into()].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != 0 {
                    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                }
            }
            posts.push(local_defs.locals[mir::RETURN_PLACE].impure_pred);

            let tcx = vcx.tcx();
            // plan:
            // - (!) collect all lifetimes
            //   - early-bound regions are substituted with the generics of the
            //     item, so we can find them in the identity substitution
            let lifetimes = GenericArgs::identity_for_item(tcx, def_id).regions()
                .into_iter()
                .collect::<Vec<_>>();
            let sig = tcx.fn_sig(def_id);
            let sig_identity = sig.instantiate_identity();
            /*
            #[derive(Debug)]
            enum SigLifetime<'tcx> {
                Early(ty::Region<'tcx>),
                Late(ty::BoundRegionKind),
            }
            let mut lifetimes = Vec::new();
            //   - early-bound regions are substituted with the generics of the
            //     item, so we can find them in the identity substitution
            lifetimes.extend(GenericArgs::identity_for_item(tcx, def_id)
                .regions()
                .map(SigLifetime::Early));
            //   - late-bound regions are found in the item's binder
            let sig = tcx.fn_sig(def_id);
            let sig_identity = sig.instantiate_identity();
            lifetimes.extend(tcx.collect_referenced_late_bound_regions(sig_identity)
                .into_iter()
                .map(SigLifetime::Late));
            println!("  lifetimes: {:?}", lifetimes);
            */

            // - (?) create longer lifetimes for input lifetimes
            //       (= lifetimes in which the arguments are covariant)
            // TODO

            // - (!) collect other outlives relations (explicit or inferred)
            //let mut outlives = Vec::new();
            let mut outlives: HashMap<ty::Region, Vec<ty::Region>> = HashMap::new();
            for (predicate, _span) in tcx.predicates_of(def_id).instantiate_identity(tcx) {
                let Some(clause_kind) = predicate.kind().no_bound_vars() else {
                    wands_println!("  predicate not handled due to non-empty binder: {predicate:?}");
                    continue;
                };
                // wands_println!("  clause: {clause_kind:?}");
                match clause_kind {
                    //ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(long, short)) => outlives.push((SigLifetime::Early(long), SigLifetime::Early(short))),
                    //ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(long, short)) => outlives.push((long, short)),
                    ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(long, short)) => outlives.entry(long)
                        .or_default()
                        .push(short),
                    // ty::ClauseKind::TypeOutlives(ty, short)
                    _ => (),
                }
            }
            wands_println!("  outlives: {:?}", outlives);

            // TODO: hardcoded...
            let ret_deref_ref = vcx.mk_local("_0r", &vir::TypeData::Ref);
            let mut ret_deref_snap = None;
            //visitor.place_overrides.insert(
            //    tcx.mk_place_deref(mir::Place::return_place()),
            //    vcx.mk_local_ex_local(ret_deref_ref),
            //);

            // - (!) collect resources associated with each lifetime
            // TODO: maybe this should happen in MirLocalDefEnc?
            let sig_identity_liberated = tcx.liberate_late_bound_regions(def_id, sig_identity);
            let mut resources_by_region = HashMap::new();
            let mut output_in_wand = None;
            for region in &lifetimes {
                use vir::Reify;
                // let SigLifetime::Early(region) = region else { continue; };
                let mut conjuncts = Vec::new();
                let mut conjuncts_in_wand = Vec::new();
                let mut places: Vec<mir::Place<'vir>> = Vec::new();
                // arguments
                for (ty, (mir_local, local)) in sig_identity_liberated.inputs().into_iter().zip(local_defs.locals.iter_enumerated().skip(1)) {
                    let indirect = deps.require_ref::<IndirectPredicatesEnc>((*ty, *region))?;
                    pres.extend(indirect.expr_pre.into_iter()
                        .map(|expr| expr.reify(vcx, local.local_ex)));
                    conjuncts.extend(indirect.expr_post.into_iter()
                        .map(|expr| expr.reify(vcx, local.local_ex)));
                    places.push(tcx.mk_place_deref(mir::Place::from(mir_local)));
                }
                // output
                {
                    let indirect = deps.require_ref::<IndirectPredicatesEnc>((sig_identity_liberated.output(), *region))?;
                    // here we use "expr_pre" to avoid wrapping in "old",
                    // because _0 does not exist in that state
                    conjuncts.extend(indirect.expr_pre.into_iter()
                        .map(|expr| expr.reify(vcx, local_defs.locals[mir::RETURN_PLACE].local_ex)));

                    // TODO: don't hardcode
                    let output_ty = sig_identity_liberated.output();
                    let output_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(output_ty).unwrap();
                    ret_deref_snap = Some(vcx.mk_local("_0s", output_ty_enc.snapshot()));
                    if let ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) = output_ty.kind() {
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                        let deref_access = output_ty_enc.generic_predicate.expect_mutref().deref_func;
                        let inner_ty_enc_c = inner_ty_enc.clone();
                        if true { //  ref_region == proj_region {
                            conjuncts_in_wand.push(inner_ty_enc.ref_to_pred(vcx, vcx.mk_local_ex_local(ret_deref_ref), None));
                            output_in_wand = Some((
                                deref_access.apply(vcx, [local_defs.locals[0usize.into()].local_ex]),
                                output_ty_enc.ref_to_snap(vcx, local_defs.locals[0usize.into()].local_ex),
                            ));
                        }
                    }
                }
                resources_by_region.insert(region, (conjuncts, conjuncts_in_wand, places));
            }
            wands_println!("  resources: {:?}", resources_by_region);

            // get method contract
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;

            // - (!) construct an outlives graph
            //       (with an "input side" and "output side")
            // - (!) unblocked resources are available in the postcondition
            // - (!) other resource must be reached by following edges,
            //       result in magic wands in the postcondition
            let mut regions_blocked = HashSet::new();
            let mut wands: Vec<(&ty::Region<'_>, Vec<&vir::ExprGenData<'_, !, !>>, Vec<&vir::ExprGenData<'vir, !, !>>, Vec<&vir::ExprGenData<'vir, !, !>>, Vec<_>)> = Vec::new();
            for region in &lifetimes {
                // is there anything to block on the input side?
                let (blocked_resources, blocked_resources_wand, blocked_places) = resources_by_region.get(&region).unwrap().clone();
                if blocked_resources_wand.is_empty() {
                    continue;
                }

                // are there regions outlived by this one?
                let Some(shorter) = outlives.get(&region) else {
                    continue;
                };

                // do these regions have any resources on the output side?
                let blocking_resources = shorter.iter()
                    .flat_map(|shorter| resources_by_region.get(&shorter).map(|e| e.0.iter()))
                    .flat_map(|res| res.into_iter())
                    .copied()
                    .collect::<Vec<_>>();
                if blocking_resources.is_empty() {
                    continue;
                }

                regions_blocked.insert(region);
                wands.push((region, blocking_resources, blocked_resources, blocked_resources_wand, blocked_places));
            }
            wands_println!("  wands: {:?}", wands);

            let unblocked_inputs = lifetimes.iter()
                .filter(|region| !regions_blocked.contains(region))
                .flat_map(|region| resources_by_region.get(&region).map(|e| e.0.iter()))
                .flat_map(|res| res.into_iter())
                .copied()
                .collect::<Vec<_>>();
            wands_println!("  unblocked inputs: {:?}", unblocked_inputs);
            posts.extend(unblocked_inputs);

            // add wands to postcondition
            struct EncodedWand<'vir> {
                wand: vir::Wand<'vir>,
                places: Vec<mir::Place<'vir>>,
                lhs_specs: Vec<vir::Expr<'vir>>,
                rhs_specs: Vec<(vir::Expr<'vir>, Span)>,
            }
            let encoded_wands = wands.into_iter()
                .map(|(_region, _lhs, rhs, lhs_wand, places)| {
                    let mut lhs_specs = Vec::new();
                    let mut rhs_specs = Vec::new();
                    if !spec.pledges.is_empty() {
                        // TODO: find corresponding pledge
                        for (lhs_expr, rhs_expr, rhs_span) in &spec.pledges {
                            if let Some(lhs_expr) = lhs_expr {
                                lhs_specs.push(*lhs_expr);
                            }
                            rhs_specs.push((*rhs_expr, *rhs_span));
                        }
                    }
                    let lhs_conjuncts = lhs_wand.iter()
                        .cloned()
                        .chain(lhs_specs.iter().copied())
                        .collect::<Vec<_>>();
                    let rhs_conjuncts = rhs.iter()
                        .cloned()
                        .chain(rhs_specs.iter().map(|(e, _)| *e))
                        .collect::<Vec<_>>();
                    let wand = vcx.mk_wand(
                        vcx.mk_conj(&lhs_conjuncts),
                        vcx.mk_conj(&rhs_conjuncts),
                    );
                    EncodedWand {
                        wand,
                        places,
                        lhs_specs,
                        rhs_specs,
                    }
                })
                .collect::<Vec<_>>();
            posts.extend(encoded_wands.iter()
                .map(|EncodedWand { wand, .. }| {
                    let mut wand_expr = vcx.mk_wand_expr(wand);
                    if let Some((expr, snap)) = output_in_wand {
                        wand_expr = vcx.mk_let_expr("_0r", expr, wand_expr);
                        wand_expr = vcx.mk_let_expr("_0s", snap, wand_expr);
                    }
                    wand_expr
                }));

            // Do not encode the method body if it is external, trusted or just
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

                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,

                    place_overrides: HashMap::new(),
                };
                visitor.visit_body(&body);

                let mut wand_packages = Vec::new();
                if let Some(final_borrow_state) = final_borrow_state {
                    // package wands
                    if let Some((expr, snap)) = output_in_wand {
                        wand_packages.push(vcx.mk_local_decl_stmt(
                            vcx.mk_local_decl_local(ret_deref_ref),
                            Some(expr),
                        ));
                        wand_packages.push(vcx.mk_local_decl_stmt(
                            vcx.mk_local_decl_local(ret_deref_snap.unwrap()),
                            Some(snap),
                        ));
                    }

                    // TODO: this is a hack! it tries to deref every argument when
                    //       creating overrides; this should only be done for ref-
                    //       typed arguments that are actually involved in a wand
                    //       (or deeper projections)
                    if !encoded_wands.is_empty() {
                        for arg_idx in 1..arg_count {
                            let local = mir::Local::from(arg_idx);
                            let deref_local = tcx.mk_place_deref(local.into());
                            let old_place = visitor.encode_place(deref_local.into());
                            visitor.place_overrides.insert(
                                deref_local,
                                vcx.mk_old_expr(old_place.expr),
                            );
                            //let name_p = local_defs.locals[arg_idx.into()].local.name;
                            //args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                            //if arg_idx != 0 {
                            //    pres.push(local_defs.locals[arg_idx.into()].impure_pred);
                            //}
                        }
                    }

                    for EncodedWand { wand, places, lhs_specs, rhs_specs } in encoded_wands {
                        //assert_eq!(places.len(), 1); // TODO ...
                        assert!(places.len() >= 1); // TODO: for now we just pick one ...
                        let blocked_place = places[0];
                        let ug = UnblockGraph::for_node(
                            blocked_place,
                            &final_borrow_state,
                            visitor.fpcs_analysis.repacker(),
                        );
                        let actions = ug.actions(visitor.fpcs_analysis.repacker()).unwrap();
                        let mut package_script = visitor.block(|visitor| {
                            visitor.pcs_unblock_actions(&actions);
                        });

                        for (spec, span) in rhs_specs {
                            vcx.with_span(span, |vcx| {
                                vcx.handle_error("exhale.failed:assertion.false", move |_| {
                                    Some(vec![PrustiError::verification(
                                        "pledge postcondition might not hold",
                                        span.into(),
                                    )])
                                });
                                package_script.push(vcx.mk_exhale_stmt(spec));
                            });
                        }
                        wand_packages.push(vcx.mk_package_stmt(
                            wand,
                            &vcx.alloc_slice(&package_script),
                        ));
                    }
                }

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

            // add basic pre- and postconditions
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
