use crate::encoders::{
    indirect::{IndirectKey, IndirectPredicatesEnc},
    ImpureEncVisitor, MirLocalDefEncOutput, MirSpecEnc,
};
use pcg::borrow_pcg::{state::BorrowsState, unblock_graph::UnblockGraph};
use prusti_interface::{environment::EnvQuery, PrustiError};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    infer::infer::region_constraints::GenericKind,
    middle::{mir, ty},
    span::{def_id::DefId, Span},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

pub type WandEncError = ();

type Pledges<'vir> = Vec<(
    Option<(vir::ExprBool<'vir>, Span)>,
    vir::ExprBool<'vir>,
    Span,
)>;

#[derive(Clone, Debug, Default)]
pub struct WandEncOutput<'vir> {
    edges: WandEncEdges,
    pub generic_to_param: FxHashMap<IndirectKey, Vec<(mir::Local, ty::Ty<'vir>)>>,
    pub pledges: Pledges<'vir>,
}

impl<'vir> WandEncOutput<'vir> {
    fn encode_generic(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: IndirectKey,
        input: bool,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> Option<vir::ExprBool<'vir>> {
        use vir::Reify;
        // There may not be any parameters for this generic, for example, if the
        // generic is the `Self` type of a trait but the function doesn't take a
        // `self` parameter.
        let param = self.generic_to_param.get(&g)?;
        let conjs = param
            .iter()
            .filter(|i| !(input && i.0 == mir::RETURN_PLACE))
            .flat_map(move |(i, ty)| {
                let indirect = deps.require_ref::<IndirectPredicatesEnc>((*ty, g)).unwrap();
                let indirect = if input == (*i == mir::RETURN_PLACE) {
                    indirect.contravariant
                } else {
                    indirect.covariant
                };
                let expr = (!indirect.is_empty()).then(|| snap(*i));
                indirect
                    .into_iter()
                    .map(move |e| e.reify(vcx, expr.unwrap()))
            });
        Some(vcx.mk_conj(vcx.alloc_slice(&conjs.collect::<Vec<_>>())))
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.inputs().filter_map(|g| {
            self.encode_generic(vcx, deps, g, true, &|i| local_defs.locals[i].impure_snap)
        })
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.outputs().filter_map(|g| {
            self.encode_generic(vcx, deps, g, false, |i| local_defs.locals[i].impure_snap)
        })
    }

    pub fn wand_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        // TODO: wands for late-bound regions
        self.viper_wands().into_iter().map(|(lhs, rhs, pledge)| {
            let mut snaps = FxHashMap::default();
            let snap_lhs = |i| {
                snaps
                    .entry(i)
                    .or_insert_with(|| {
                        let name = vir::vir_format!(vcx, "wand{:?}", i);
                        (
                            name,
                            vcx.mk_local_ex(name, local_defs.locals[i].ty.snapshot),
                        )
                    })
                    .1
            };
            let snap_rhs = |i| vcx.mk_old_expr(local_defs.locals[i].impure_snap);
            match self.mk_wand(&lhs, &rhs, &pledge, snap_lhs, snap_rhs, vcx, deps) {
                Ok(wand) => {
                    snaps
                        .into_iter()
                        .fold(vcx.mk_wand_expr(wand), |acc, (local, (name, _))| {
                            vcx.mk_let_expr(name, local_defs.locals[local].impure_snap, acc)
                        })
                }
                Err(rhs) => rhs,
            }
        })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::ExprSnap<'vir>],
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
        for (lhs, rhs, pledge) in self.viper_wands() {
            if lhs.is_empty() {
                continue;
            }
            let wand = self
                .mk_wand(&lhs, &rhs, &pledge, snap_lhs, snap_rhs, vcx, visitor.deps)
                .unwrap();
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

        for (lhs, rhs, pledge) in self.viper_wands() {
            if lhs.is_empty() {
                continue;
            }
            let wand = self
                .mk_wand(&lhs, &rhs, &pledge, snap_lhs, snap_rhs, vcx, visitor.deps)
                .unwrap();
            let mut package_script = Vec::new();
            for (rhs, _) in rhs
                .iter()
                .filter(|g| self.generic_to_param.contains_key(g))
                .flat_map(|g| &self.generic_to_param[g])
            {
                if *rhs == mir::RETURN_PLACE {
                    continue;
                }
                let ug = UnblockGraph::for_node(
                    mir::Place::from(*rhs),
                    final_borrow_state,
                    visitor.pcg_ctxt(),
                );
                let actions = ug.actions(visitor.pcg_ctxt()).unwrap();
                let unblock = visitor.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, Some(label));
                });
                package_script.extend(unblock);
            }

            for &(_, spec, span) in pledge.iter() {
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

    fn mk_wand<'a, E: TaskEncoder>(
        &'a self,
        lhs: &[IndirectKey],
        rhs: &[IndirectKey],
        pledge: &Pledges<'vir>,
        mut snap_lhs: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
        mut snap_rhs: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<vir::Wand<'vir>, vir::ExprBool<'vir>> {
        let rhs = rhs
            .iter()
            .filter_map(|g| self.encode_generic(vcx, deps, *g, true, &mut snap_rhs));
        let rhs = rhs.chain(pledge.iter().map(|(_, rhs, _)| *rhs));
        let rhs = vcx.mk_conj(vcx.alloc_slice(&rhs.collect::<Vec<_>>()));
        if lhs.is_empty() {
            return Err(rhs);
        }
        let lhs = lhs
            .iter()
            .filter_map(|g| self.encode_generic(vcx, deps, *g, false, &mut snap_lhs));
        let lhs = lhs.chain(
            pledge
                .iter()
                .filter_map(|(lhs, _, _)| lhs.map(|(lhs, _)| lhs)),
        );
        let lhs = vcx.mk_conj(vcx.alloc_slice(&lhs.collect::<Vec<_>>()));
        Ok(vcx.mk_wand(lhs, rhs))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WandEncTask {
    pub def_id: DefId,
}

#[derive(Clone, Debug, Default)]
struct WandEncEdges {
    /// for b in inputs { requires b }
    inputs: Vec<IndirectKey>,
    /// for a in outputs { ensures a }
    outputs: Vec<IndirectKey>,
    /// for (a, b) in edges { ensures a --* b }
    edges: Vec<(IndirectKey, IndirectKey)>,
}

impl WandEncEdges {
    fn input(&mut self, key: IndirectKey) {
        debug_assert!(!self.inputs.contains(&key), "input {key:?} already exists");
        self.inputs.push(key);
    }

    fn output(&mut self, key: IndirectKey) {
        debug_assert!(
            !self.outputs.contains(&key),
            "output {key:?} already exists"
        );
        self.outputs.push(key);
    }

    fn input_and_output(&mut self, key: IndirectKey, skip_output: bool) {
        if !skip_output {
            self.output(key);
        }
        self.input(key);
        self.edge(key, key);
    }

    /// Adds an edge of `output --* input`.
    fn edge(&mut self, output: IndirectKey, input: IndirectKey) {
        debug_assert!(
            self.inputs.contains(&input),
            "input {input:?} does not exist"
        );
        debug_assert!(
            self.outputs.contains(&output),
            "output {output:?} does not exist"
        );
        debug_assert!(
            !self.edges.contains(&(output, input)),
            "edge {output:?} --* {input:?} already exists"
        );
        let output_param = matches!(output, IndirectKey::Param(..));
        let input_param = matches!(input, IndirectKey::Param(..));
        if input_param ^ output_param {
            // TODO: handle generics that are instantiated with a lifetime type
            // and are nested under another lifetime, e.g.
            // fn foo<T>(x: &mut T) -> &mut T (with `T -> &mut i32`)
            return;
        }
        self.edges.push((output, input));
    }
}

impl TaskEncoder for WandEnc {
    task_encoder::encoder_cache!(WandEnc);

    type TaskDescription<'vir> = WandEncTask;

    type TaskKey<'vir> = WandEncTask;

    type OutputFullLocal<'vir> = WandEncOutput<'vir>;

    type EncodingError = WandEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        WandEncTask {
            def_id: task.def_id,
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id;
            let tcx = vcx.tcx();
            let ecx = EnvQuery::new(tcx);
            let substs = ecx.identity_substs(def_id);

            let fn_sig = ecx.get_fn_sig(def_id, substs);
            let args = [fn_sig.skip_binder().output()]
                .into_iter()
                .chain(fn_sig.skip_binder().inputs().iter().copied())
                .enumerate();
            let mut generic_to_param: FxHashMap<IndirectKey, Vec<_>> = Default::default();

            let mut gidx_map: FxHashMap<IndirectKey, Result<ty::Variance, usize>> =
                Default::default();
            let mut edges = WandEncEdges::default();

            for (i, ty) in args {
                for ga in ty.walk() {
                    let Some(key) = IndirectKey::from_generic_arg(ga) else {
                        continue;
                    };
                    let local = mir::Local::from_usize(i);
                    if let IndirectKey::Late(..) = key {
                        // A late bound lifetime is guaranteed to not be nested
                        // (otherwise it would have an outlives and not be late bound).
                        if local == mir::RETURN_PLACE {
                            match gidx_map.insert(key, Ok(ty::Variance::Covariant)) {
                                Some(Ok(ty::Variance::Covariant)) => {}
                                None => edges.output(key),
                                _ => unreachable!(),
                            }
                        } else {
                            use std::collections::hash_map::Entry;
                            match gidx_map.entry(key) {
                                Entry::Occupied(mut o) => match o.get() {
                                    Ok(ty::Variance::Covariant) => {
                                        o.insert(Ok(ty::Variance::Invariant)).ok();
                                        edges.input_and_output(key, true);
                                    }
                                    Ok(ty::Variance::Contravariant | ty::Variance::Invariant) => {}
                                    _ => unreachable!(),
                                },
                                Entry::Vacant(v) => {
                                    v.insert(Ok(ty::Variance::Contravariant));
                                    edges.input(key);
                                }
                            }
                        }
                    }
                    generic_to_param.entry(key).or_default().push((local, ty));
                }
            }

            let outlives_env = ecx.outlives_env(def_id);

            let variances = tcx.variances_of(def_id);
            let generics = tcx.generics_of(def_id);
            assert_eq!(generics.count(), variances.len());
            // Old way of collecting late bound regions, not used anymore.
            debug_assert!(
                generics.has_late_bound_regions.is_some()
                    || tcx.collect_referenced_late_bound_regions(fn_sig).is_empty()
            );

            for i in 0..generics.count() {
                let g = generics.param_at(i, tcx);
                let key = match g.kind {
                    ty::GenericParamDefKind::Lifetime => {
                        IndirectKey::Early(g.to_early_bound_region_data())
                    }
                    ty::GenericParamDefKind::Type { .. } => IndirectKey::Param(ty::ParamTy {
                        index: g.index,
                        name: g.name,
                    }),
                    // TODO: skip here?
                    ty::GenericParamDefKind::Const { .. } => continue,
                };
                gidx_map.insert(key, Err(i));
                match variances[i] {
                    ty::Variance::Covariant => {
                        edges.output(key);
                    }
                    ty::Variance::Contravariant => {
                        edges.input(key);
                    }
                    ty::Variance::Invariant => {
                        edges.input_and_output(key, false);
                    }
                    ty::Variance::Bivariant => todo!("not sure what this means/how to handle it"),
                }
            }

            // `b` outlives `a`
            let mut insert_edge = |a, b| {
                let (v_a, v_b) = (
                    gidx_map[&a].unwrap_or_else(|i| variances[i]),
                    gidx_map[&b].unwrap_or_else(|i| variances[i]),
                );
                if let (
                    ty::Variance::Covariant | ty::Variance::Invariant,
                    ty::Variance::Contravariant | ty::Variance::Invariant,
                ) = (v_a, v_b)
                {
                    edges.edge(a, b);
                }
            };

            let frm = outlives_env.free_region_map();
            let rbp = outlives_env.region_bound_pairs();

            // FIXME: hopefully the quadratic thing here isn't an issue
            for r_a in frm.elements() {
                for r_b in frm.elements() {
                    if r_a == r_b {
                        continue;
                    }
                    if !frm.sub_free_regions(tcx, r_a, r_b) {
                        continue;
                    }
                    let (ty::RegionKind::ReEarlyParam(a), ty::RegionKind::ReEarlyParam(b)) =
                        (r_a.kind(), r_b.kind())
                    else {
                        todo!("region bound pair: ({r_a:?}, {r_b:?})");
                    };
                    insert_edge(IndirectKey::Early(a), IndirectKey::Early(b));
                }
            }

            for pred in rbp {
                let GenericKind::Param(b) = pred.0 else {
                    todo!("region bound pair: {pred:?}");
                };
                let Some(a) = IndirectKey::from_region(pred.1) else {
                    todo!("region bound pair: {pred:?}");
                };
                // This edge may be skipped, see TODO in `WandEncEdges::edge`.
                insert_edge(a, IndirectKey::Param(b));
            }

            let spec = deps.require_local::<MirSpecEnc>((def_id, substs, None, false))?;

            Ok((
                WandEncOutput {
                    edges,
                    generic_to_param,
                    pledges: spec.pledges,
                },
                (),
            ))
        })
    }
}

impl<'vir> WandEncOutput<'vir> {
    pub fn inputs(&self) -> impl Iterator<Item = IndirectKey> + '_ {
        self.edges.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = IndirectKey> + '_ {
        self.edges.outputs.iter().copied()
    }

    pub fn edges(&self) -> impl Iterator<Item = (IndirectKey, IndirectKey)> + '_ {
        self.edges.edges.iter().copied()
    }

    /// convert edges to viper-supported wands
    pub fn viper_wands(&self) -> Vec<(Vec<IndirectKey>, Vec<IndirectKey>, Pledges<'vir>)> {
        // Indexed by the `rhs` of wands
        let mut edge_rhs: FxHashMap<IndirectKey, Vec<IndirectKey>> = Default::default();
        // Indexed by the `lhs` of wands
        let mut edge_lhs: FxHashMap<IndirectKey, Vec<IndirectKey>> = Default::default();
        let mut wands: Vec<(Vec<IndirectKey>, Vec<IndirectKey>, Pledges<'vir>)> =
            Default::default();

        for (lhs, rhs) in self.edges() {
            edge_lhs.entry(lhs).or_default().push(rhs);
            edge_rhs.entry(rhs).or_default().push(lhs);
        }

        let mut skip = FxHashSet::default();
        for rhs in self.inputs() {
            if !skip.insert(rhs) {
                continue;
            }
            let Some(lhss) = edge_rhs.get(&rhs) else {
                wands.push((vec![], vec![rhs], vec![]));
                continue;
            };
            let lhs = lhss.first().unwrap();
            let rhss = &edge_lhs[lhs];
            for lhs_other in lhss {
                let rhss_other = &edge_lhs[lhs_other];
                assert_eq!(rhss, rhss_other, "two outputs do not block the same set of inputs: {lhs:?} blocks {rhss:?}, {lhs_other:?} blocks {rhss_other:?}");
            }
            for rhs_other in rhss {
                let lhss_other = &edge_rhs[rhs_other];
                assert_eq!(lhss, lhss_other, "two inputs are not blocked by the same set of outputs: {rhs:?} blocked by {lhss:?}, {rhs_other:?} blocked by {lhss_other:?}");
            }
            wands.push((lhss.clone(), rhss.clone(), vec![]));
            skip.extend(rhss);
        }
        if !self.pledges.is_empty() {
            let mut actual_wands = wands.iter_mut().filter(|(lhs, ..)| !lhs.is_empty());
            let wand = actual_wands.next();
            assert!(wand.is_some(), "pledge for function with no wands");
            assert!(
                actual_wands.next().is_none(),
                "pledge for function with multiple wands"
            );
            wand.unwrap().2 = self.pledges.clone();
        }
        wands
    }
}
