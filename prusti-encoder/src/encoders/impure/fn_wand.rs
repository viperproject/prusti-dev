use crate::encoders::{
    indirect::IndirectPredicatesEnc, ImpureEncVisitor, MirLocalDefEncOutput, MirSpecEnc,
};
use pcg::borrow_pcg::{state::BorrowsState, unblock_graph::UnblockGraph};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::{
        mir,
        ty::{self, GenericArgs},
    },
    span::{def_id::DefId, Span},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

pub type WandEncError = ();

#[derive(Clone, Debug, Default)]
pub struct WandEncOutput<'vir> {
    pub encoded_wands: Vec<EncodedWand<'vir>>,
    pub indirect_pres: Vec<(ty::Region<'vir>, mir::Local, ty::Ty<'vir>)>,
    pub indirect_posts: Vec<(ty::Region<'vir>, mir::Local, ty::Ty<'vir>)>,
}

#[derive(Clone, Debug)]
pub struct EncodedWand<'vir> {
    pub region: ty::Region<'vir>,
    pub lhs_resources: Vec<(ty::Region<'vir>, mir::Local, ty::Ty<'vir>)>,
    pub rhs_resources: Vec<(mir::Local, ty::Ty<'vir>)>,
    pub lhs_specs: Vec<(vir::Expr<'vir>, Span)>,
    pub rhs_specs: Vec<(vir::Expr<'vir>, Span)>,
}

impl<'vir> EncodedWand<'vir> {
    pub fn mk_wand<'a, E: TaskEncoder>(
        &'a self,
        mut snap_lhs: impl FnMut(mir::Local) -> vir::Expr<'vir>,
        mut snap_rhs: impl FnMut(mir::Local) -> vir::Expr<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> vir::Wand<'vir> {
        use vir::Reify;
        let mut resource_to_expr =
            |(region, local, ty): (ty::Region<'vir>, mir::Local, ty::Ty<'vir>)| {
                let indirect = deps
                    .require_ref::<IndirectPredicatesEnc>((ty, region))
                    .unwrap();
                indirect.expr.into_iter().map(move |e| (local, e))
            };
        let lhs = self
            .lhs_resources
            .iter()
            .copied()
            .flat_map(&mut resource_to_expr)
            .map(|(l, expr)| expr.reify(vcx, snap_lhs(l)))
            .chain(self.lhs_specs.iter().map(|(e, _)| *e))
            .collect::<Vec<_>>();
        let rhs = self
            .rhs_resources
            .iter()
            .map(|(l, t)| (self.region, *l, *t))
            .flat_map(&mut resource_to_expr)
            .map(|(l, expr)| expr.reify(vcx, snap_rhs(l)))
            .chain(self.rhs_specs.iter().map(|(e, _)| *e))
            .collect::<Vec<_>>();
        let lhs = vcx.mk_conj(vcx.alloc_slice(&lhs));
        let rhs = vcx.mk_conj(vcx.alloc_slice(&rhs));
        vcx.mk_wand(lhs, rhs)
    }
}

impl<'vir> WandEncOutput<'vir> {
    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::Expr<'vir>> + 'a {
        use vir::Reify;
        self.indirect_pres.iter().flat_map(|(region, local, ty)| {
            let indirect = deps
                .require_ref::<IndirectPredicatesEnc>((*ty, *region))
                .unwrap();
            let expr = local_defs.locals[*local].impure_snap;
            indirect.expr.into_iter().map(|e| e.reify(vcx, expr))
        })
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::Expr<'vir>> + 'a {
        use vir::Reify;
        self.indirect_posts.iter().flat_map(|(region, local, ty)| {
            let indirect = deps
                .require_ref::<IndirectPredicatesEnc>((*ty, *region))
                .unwrap();
            let mut expr = local_defs.locals[*local].impure_snap;
            if *local != mir::RETURN_PLACE {
                expr = vcx.mk_old_expr(expr);
            }
            indirect.expr.into_iter().map(|e| e.reify(vcx, expr))
        })
    }

    pub fn wand_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::Expr<'vir>> + 'a {
        let return_ = &local_defs.locals[mir::RETURN_PLACE];
        let var_name = "_0_wand";
        let tmp_ex = vcx.mk_local_ex(var_name, return_.ty.snapshot);
        self.encoded_wands.iter().map(move |ewand| {
            let mut uses_return = false;
            let snap_lhs = |l| {
                if l == mir::RETURN_PLACE {
                    uses_return = true;
                    tmp_ex
                } else {
                    vcx.mk_old_expr(local_defs.locals[l].impure_snap)
                }
            };
            let snap_rhs = |l| vcx.mk_old_expr(local_defs.locals[l].impure_snap);
            let wand = vcx.mk_wand_expr(ewand.mk_wand(snap_lhs, snap_rhs, vcx, deps));
            if uses_return {
                vcx.mk_let_expr(var_name, return_.impure_snap, wand)
            } else {
                wand
            }
        })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::Expr<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) {
        let vcx = visitor.vcx;
        let snap_lhs = |l: mir::Local| {
            if l == mir::RETURN_PLACE {
                vcx.mk_local_labelled_old_expr(arguments[l.as_usize()], label_post)
            } else {
                vcx.mk_local_labelled_old_expr(arguments[l.as_usize()], label_pre)
            }
        };
        let snap_rhs =
            |l: mir::Local| vcx.mk_local_labelled_old_expr(arguments[l.as_usize()], label_pre);
        for ewand in &self.encoded_wands {
            let wand = ewand.mk_wand(snap_lhs, snap_rhs, vcx, visitor.deps);
            visitor.stmt(visitor.vcx.mk_apply_stmt(wand));
        }
    }

    pub fn package_wands<E: TaskEncoder>(
        &self,
        final_borrow_state: &BorrowsState<'vir>,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) -> Vec<vir::Stmt<'vir>> {
        let mut wand_packages = Vec::new();
        let vcx = visitor.vcx;
        let label = visitor.new_label("package_post");
        let snap_lhs = |l| {
            if l == mir::RETURN_PLACE {
                vcx.mk_local_labelled_old_expr(visitor.local_defs.locals[l].impure_snap, label)
            } else {
                vcx.mk_old_expr(visitor.local_defs.locals[l].impure_snap)
            }
        };
        let snap_rhs = |l| vcx.mk_old_expr(visitor.local_defs.locals[l].impure_snap);

        for ewand in &self.encoded_wands {
            let wand = ewand.mk_wand(snap_lhs, snap_rhs, vcx, visitor.deps);
            let mut package_script = Vec::new();
            for (rhs, _) in ewand.rhs_resources.iter().copied() {
                let ug = UnblockGraph::for_node(
                    mir::Place::from(rhs),
                    final_borrow_state,
                    visitor.pcg_ctxt(),
                );
                let actions = ug.actions(visitor.pcg_ctxt()).unwrap();
                let unblock = visitor.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, Some(label));
                });
                package_script.extend(unblock);
            }

            for &(spec, span) in ewand.rhs_specs.iter() {
                visitor.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pledge postcondition might not hold",
                            span.into(),
                        )])
                    });
                    package_script.push(vcx.mk_exhale_stmt(spec));
                });
            }
            wand_packages.push(
                visitor
                    .vcx
                    .mk_package_stmt(wand, visitor.vcx.alloc_slice(&package_script)),
            );
        }
        wand_packages
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

    type OutputFullLocal<'vir> = WandEncOutput<'vir>;

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

            // Collect all early-boundy lifetimes. These are generics, same as
            // type params, so we can find them in the identity substitution.
            let lifetimes = GenericArgs::identity_for_item(tcx, def_id)
                .regions()
                .collect::<Vec<_>>();
            let sig = tcx.fn_sig(def_id);
            let sig_identity = sig.instantiate_identity();

            // TODO: what about late-bound regions? In function signatures such
            //   as this reborrowing function:
            // ```rust
            // fn reborrow(x: &mut (i32, i32)) -> &mut i32 { &mut x.0 }
            // ```
            //   the lifetimes are *not* early-bound, but we still want a magic
            //   wand to represent the reborrow.
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

            // TODO: consider variance of arguments wrt. each lifetime.

            // Collect outlives relations, both explicit (e.g. declared in a
            // `where` clause) and inferred (e.g. due to type nesting).
            let mut outlives: FxHashMap<ty::Region, Vec<ty::Region>> = FxHashMap::default();
            for (predicate, _span) in tcx.predicates_of(def_id).instantiate_identity(tcx) {
                let Some(clause_kind) = predicate.kind().no_bound_vars() else {
                    wands_println!(
                        "  predicate not handled due to non-empty binder: {predicate:?}"
                    );
                    continue;
                };
                // TODO: there may be other clauses which might be important
                //   for wands? In paritcular, see `TypeOutlives`.`
                if let ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(long, short)) =
                    clause_kind
                {
                    if long == short {
                        continue;
                    }
                    outlives.entry(long).or_default().push(short)
                }
            }
            wands_println!("  outlives: {:?}", outlives);

            // Associate resources to lifetimes. At this point, we will only
            // walk the inputs and output types of the function to find ones
            // which mention the given lifetime *at all*, regardless of its
            // function/variance in the type. Later, the indirect encoder will
            // be invoked on these to get the concrete predicates.
            let sig_identity_liberated = tcx.liberate_late_bound_regions(def_id, sig_identity);
            // let locals = sig_identity_liberated.inputs_and_output
            //     .iter()
            //     .enumerate()
            //     .map(|(local, ty)| {
            //         vcx.mk_lazy_expr(
            //             vir::vir_format!(vcx, "wand in _{local}"),
            //             &vir::TypeData::Ref,
            //             Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[local - 1].kind),
            //         )
            //     })
            //     .collect::<Vec<_>>();
            let mut resources_by_region: FxHashMap<
                &ty::Region<'_>,
                Vec<(mir::Local, ty::Ty<'vir>)>,
            > = FxHashMap::default();
            for region in &lifetimes {
                // let SigLifetime::Early(region) = region else { continue; };
                let mut resources = Vec::new();
                let inputs = sig_identity_liberated
                    .inputs()
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| (mir::Local::from(i + 1), *ty));
                let output_and_inputs = [(mir::RETURN_PLACE, sig_identity_liberated.output())]
                    .into_iter()
                    .chain(inputs);
                for (local_idx, ty) in output_and_inputs {
                    if !ty.walk().any(|t| t.as_region() == Some(*region)) {
                        continue;
                    }
                    resources.push((local_idx, ty));
                }
                resources_by_region.insert(region, resources);
            }
            wands_println!("  resources: {:?}", resources_by_region);

            // Construct a graph of resources, related by the outlives edges.
            // TODO: at the moment, we will only construct a bipartite graph;
            //   sometimes a more complex shape should be constructed?
            let mut indirect_pres = Vec::new();
            let mut indirect_posts = Vec::new();
            let mut wands: Vec<(
                ty::Region<'_>,
                Vec<(ty::Region<'_>, mir::Local, ty::Ty<'vir>)>,
                Vec<(mir::Local, ty::Ty<'vir>)>,
            )> = Vec::new();
            for region in &lifetimes {
                // is there anything to block on the input side?
                let blocked_resources = &resources_by_region[&region];
                if blocked_resources.is_empty() {
                    continue;
                }

                indirect_pres.extend(
                    blocked_resources
                        .iter()
                        .filter(|(l, _)| *l != mir::RETURN_PLACE)
                        .map(|(l, t)| (*region, *l, *t)),
                );
                // are there regions outlived by this one?
                let Some(shorter) = outlives.get(region) else {
                    indirect_posts.extend(blocked_resources.iter().map(|(l, t)| (*region, *l, *t)));
                    continue;
                };

                // do these regions have any resources on the output side?
                let blocking_resources = shorter
                    .iter()
                    .filter_map(|shorter| {
                        resources_by_region
                            .get(&shorter)
                            .map(|e| e.iter().map(|(l, t)| (*shorter, *l, *t)))
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                if blocking_resources.is_empty() {
                    indirect_posts.extend(blocked_resources.iter().map(|(l, t)| (*region, *l, *t)));
                    continue;
                }

                wands.push((*region, blocking_resources, blocked_resources.clone()));
            }
            wands_println!("  wands: {:?}", wands);

            // Collect pledge specifications and add them to wands.
            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;
            let encoded_wands: Vec<EncodedWand<'vir>> = wands
                .into_iter()
                .map(|(region, lhs_resources, rhs_resources)| {
                    let mut lhs_specs: Vec<(vir::Expr<'vir>, Span)> = Vec::new();
                    let mut rhs_specs: Vec<(vir::Expr<'vir>, Span)> = Vec::new();
                    if !spec.pledges.is_empty() {
                        // TODO: find the corresponding pledge, also the pledges should expect to be reified with the locals
                        for (lhs_expr, rhs_expr, rhs_span) in &spec.pledges {
                            if let Some((lhs_expr, lhs_span)) = lhs_expr {
                                lhs_specs.push((lhs_expr, *lhs_span));
                            }
                            rhs_specs.push((rhs_expr, *rhs_span));
                        }
                    }
                    EncodedWand {
                        region,
                        lhs_resources,
                        rhs_resources,
                        lhs_specs,
                        rhs_specs,
                    }
                })
                .collect::<Vec<_>>();

            Ok((
                WandEncOutput {
                    encoded_wands,
                    indirect_pres,
                    indirect_posts,
                },
                (),
            ))
        })
    }
}
