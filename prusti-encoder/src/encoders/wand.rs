use std::{collections::{HashMap, HashSet}, rc::Rc};

use pcs::borrow_pcg::{state::BorrowsState, unblock_graph::UnblockGraph};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    middle::{mir, ty::{self, GenericArgs}},
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::{encoder_traits::impure_function_enc::ImpureFunctionEnc, encoders::{indirect::IndirectPredicatesEnc, rust_ty_predicates::RustTyPredicatesEnc, MirSpecEnc}};

use super::ImpureEncVisitor;

pub struct WandEnc;

pub type WandEncError = ();

type ExprInput<'vir> = (DefId, &'vir [vir::Expr<'vir>]);
//type ExprRet<'vir> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

#[derive(Clone, Debug)]
pub struct WandEncOutput<'vir, Curr: 'vir, Next: 'vir> {
    pub encoded_wands: Vec<EncodedWand<'vir, Curr, Next>>,
    pub output_in_wand: Option<(vir::ExprGen<'vir, Curr, Next>, vir::ExprGen<'vir, Curr, Next>)>,
    pub indirect_pres: Vec<vir::ExprGen<'vir, Curr, Next>>,
    pub indirect_posts: Vec<vir::ExprGen<'vir, Curr, Next>>,
    ret_deref_ref: vir::Local<'vir>,
    ret_deref_snap: Option<vir::Local<'vir>>,
    arg_count: usize,
}

#[derive(Clone, Debug)]
pub struct EncodedWand<'vir, Curr: 'vir, Next: 'vir> {
    pub wand: vir::WandGen<'vir, Curr, Next>,
    pub places: Vec<mir::Place<'vir>>,
    pub lhs_specs: Vec<vir::ExprGen<'vir, Curr, Next>>,
    pub rhs_specs: Vec<(vir::ExprGen<'vir, Curr, Next>, Span)>,
}

impl<'vir> vir::Reify<'vir, ExprInput<'vir>> for WandEncOutput<'vir, ExprInput<'vir>, vir::ExprKind<'vir>> {
    type Next = WandEncOutput<'vir, !, !>;

    fn reify<'tcx>(&self, vcx: &'vir vir::VirCtxt<'tcx>, lctx: ExprInput<'vir>) -> Self::Next {
        WandEncOutput {
            encoded_wands: self.encoded_wands.iter()
                .map(|w| EncodedWand {
                    wand: w.wand.reify(vcx, lctx),
                    places: w.places.clone(),
                    lhs_specs: w.lhs_specs.reify(vcx, lctx).to_vec(),
                    rhs_specs: w.rhs_specs.iter()
                        .map(|(e, span)| (e.reify(vcx, lctx), *span))
                        .collect(),
                })
                .collect(),
            output_in_wand: self.output_in_wand
                .map(|(l, r)| (l.reify(vcx, lctx), r.reify(vcx, lctx))),
            indirect_pres: self.indirect_pres.reify(vcx, lctx).to_vec(),
            indirect_posts: self.indirect_posts.reify(vcx, lctx).to_vec(),
            ret_deref_ref: self.ret_deref_ref,
            ret_deref_snap: self.ret_deref_snap,
            arg_count: self.arg_count,
        }
    }
}

impl<'vir> WandEncOutput<'vir, !, !> {
    pub fn package_wands<E: ImpureFunctionEnc>(
        &self,
        final_borrow_state: Rc<BorrowsState<'vir>>,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) -> Vec<vir::Stmt<'vir>> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let mut wand_packages = Vec::new();
            // package wands
            if let Some((expr, snap)) = self.output_in_wand {
                wand_packages.push(vcx.mk_local_decl_stmt(
                    vcx.mk_local_decl_local(self.ret_deref_ref),
                    Some(expr),
                ));
                wand_packages.push(vcx.mk_local_decl_stmt(
                    vcx.mk_local_decl_local(self.ret_deref_snap.unwrap()),
                    Some(snap),
                ));
            }

            // TODO: this is a hack! it tries to deref every argument when
            //       creating overrides; this should only be done for ref-
            //       typed arguments that are actually involved in a wand
            //       (or deeper projections)
            if !self.encoded_wands.is_empty() {
                for arg_idx in 1..self.arg_count {
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

            for EncodedWand { wand, places, lhs_specs, rhs_specs } in self.encoded_wands.clone() {
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

            wand_packages
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WandEncTask<'tcx> {
    pub def_id: DefId,
    pub substs: ty::GenericArgsRef<'tcx>,
}

macro_rules! wands_println {
    ($($args:tt)*) => {
        // println!($($args)*)
    };
}

impl TaskEncoder for WandEnc {
    task_encoder::encoder_cache!(WandEnc);

    type TaskDescription<'vir> = WandEncTask<'vir>;

    type TaskKey<'vir> = WandEncTask<'vir>;

    type OutputFullLocal<'vir> = WandEncOutput<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;

    type EncodingError = WandEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        WandEncTask {
            def_id: task.def_id,
            substs: task.substs,
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id;
            let substs = task_key.substs;
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
            let arg_count = sig_identity_liberated.inputs_and_output.len();
            let locals = sig_identity_liberated.inputs_and_output
                .iter()
                .enumerate()
                .map(|(local, ty)| {
                    vcx.mk_lazy_expr(
                        vir::vir_format!(vcx, "wand in _{local}"),
                        &vir::TypeData::Ref,
                        Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[local - 1].kind),
                    )
                })
                .collect::<Vec<_>>();
            let mut resources_by_region: HashMap<
                &ty::Region<'_>,
                (
                    Vec<&vir::ExprGenData<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>>,
                    Vec<&vir::ExprGenData<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>>,
                    Vec<mir::Place<'vir>>,
                ),
            > = HashMap::new();
            let mut output_in_wand = None;
            let mut indirect_pres = Vec::new();
            for region in &lifetimes {
                use vir::Reify;
                // let SigLifetime::Early(region) = region else { continue; };
                let mut conjuncts = Vec::new();
                let mut conjuncts_in_wand = Vec::new();
                let mut places: Vec<mir::Place<'vir>> = Vec::new();
                // arguments
                for (ty, (local_idx, local_ex)) in sig_identity_liberated.inputs().into_iter().zip(locals.iter().enumerate().skip(1)) {
                    let indirect = deps.require_ref::<IndirectPredicatesEnc>((*ty, *region))?;
                    indirect_pres.extend(indirect.expr_pre.into_iter()
                        .map(|expr| vcx.mk_lazy_expr(
                            "wand_arg_indirect_pre", // &format!("wand_arg{local_idx}_indirect_pre"),
                            &vir::TypeData::Predicate,
                            Box::new(move |vcx, lctx: ExprInput<'_>| (expr.reify(vcx, lctx.1[local_idx])).kind),
                        )));
                        // expr.reify(vcx, local_ex)));
                    conjuncts.extend(indirect.expr_post.into_iter()
                        .map(|expr| vcx.mk_lazy_expr(
                            "wand_arg_indirect_post", // &format!("wand_arg{local_idx}_post"),
                            &vir::TypeData::Predicate,
                            Box::new(move |vcx, lctx: ExprInput<'_>| (expr.reify(vcx, lctx.1[local_idx])).kind),
                        )));
                        //.map(|expr| expr.reify(vcx, local_ex)));
                    places.push(tcx.mk_place_deref(mir::Place::from(mir::Local::from(local_idx))));
                }
                // output
                {
                    let indirect = deps.require_ref::<IndirectPredicatesEnc>((sig_identity_liberated.output(), *region))?;
                    // here we use "expr_pre" to avoid wrapping in "old",
                    // because _0 does not exist in that state
                    conjuncts.extend(indirect.expr_pre.into_iter()
                        .map(|expr| vcx.mk_lazy_expr(
                            "wand_ret_post",
                            &vir::TypeData::Predicate,
                            Box::new(move |vcx, lctx: ExprInput<'_>| (expr.reify(vcx, lctx.1[0])).kind),
                        )));
                        // .map(|expr| expr.reify(vcx, locals[0])));

                    // TODO: don't hardcode
                    let output_ty = sig_identity_liberated.output();
                    let output_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(output_ty).unwrap();
                    ret_deref_snap = Some(vcx.mk_local("_0s", output_ty_enc.snapshot()));
                    if let ty::TyKind::Ref(ref_region, inner_ty, ty::Mutability::Mut) = output_ty.kind() {
                        let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                        let deref_access = output_ty_enc.generic_predicate.expect_mutref().deref_func;
                        let inner_ty_enc_c = inner_ty_enc.clone();
                        if true { //  ref_region == proj_region {
                            conjuncts_in_wand.push(vcx.mk_lazy_expr(
                                "wand_output",
                                &vir::TypeData::Predicate,
                                Box::new(move |vcx, lctx: ExprInput<'_>| inner_ty_enc
                                    .ref_to_pred(vcx, vcx.mk_local_ex_local(ret_deref_ref), None)
                                    .kind),
                            ));
                            // conjuncts_in_wand.push(inner_ty_enc.ref_to_pred(vcx, vcx.mk_local_ex_local(ret_deref_ref), None));
                            output_in_wand = Some((
                                vcx.mk_lazy_expr(
                                    "wand_outputn",
                                    &vir::TypeData::Predicate,
                                    Box::new(move |vcx, lctx: ExprInput<'_>| deref_access.apply(vcx, [lctx.1[0]]).kind),
                                ),
                                //deref_access.apply(vcx, [locals[0]]),
                                vcx.mk_lazy_expr(
                                    "wand_output2",
                                    &vir::TypeData::Predicate,
                                    Box::new(move |vcx, lctx: ExprInput<'_>| output_ty_enc
                                        .ref_to_snap(vcx, lctx.1[0])
                                        .kind),
                                ),
                                // output_ty_enc.ref_to_snap(vcx, locals[0]),
                            ));
                        }
                    }
                }
                resources_by_region.insert(region, (conjuncts, conjuncts_in_wand, places));
            }
            wands_println!("  resources: {:?}", resources_by_region);

            // - (!) construct an outlives graph
            //       (with an "input side" and "output side")
            // - (!) unblocked resources are available in the postcondition
            // - (!) other resource must be reached by following edges,
            //       result in magic wands in the postcondition
            let mut regions_blocked = HashSet::new();
            let mut wands: Vec<(
                &ty::Region<'_>,
                Vec<&vir::ExprGenData<'_, ExprInput<'vir>, vir::ExprKind<'vir>>>,
                Vec<&vir::ExprGenData<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>>,
                Vec<&vir::ExprGenData<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>>,
                Vec<_>,
            )> = Vec::new();
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
            //posts.extend(unblocked_inputs);

            // add wands to postcondition
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;
            let encoded_wands: Vec<EncodedWand<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>> = wands.into_iter()
                .map(|(_region, _lhs, rhs, lhs_wand, places)| {
                    let mut lhs_specs: Vec<vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>> = Vec::new();
                    let mut rhs_specs: Vec<(vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>, Span)> = Vec::new();
                    if !spec.pledges.is_empty() {
                        // TODO: find corresponding pledge
                        for (lhs_expr, rhs_expr, rhs_span) in &spec.pledges {
                            if let Some(lhs_expr) = lhs_expr {
                                lhs_specs.push(lhs_expr.lift());
                            }
                            rhs_specs.push((rhs_expr.lift(), *rhs_span));
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

            Ok((WandEncOutput {
                encoded_wands,
                output_in_wand,
                indirect_pres,
                indirect_posts: Vec::new(),
                ret_deref_ref,
                ret_deref_snap,
                arg_count,
            }, ()))
        })
    }
}
