use crate::encoders::{
    EncodeResult, ImpureEncVisitor, MirLocalDefEncOutput, MirSpecEnc,
    pure::spec::{EncodedPledge, MirSpecEncMode, PledgeArgs, PledgeExpr},
    ty::{
        RustTyDecomposition,
        generics::{GArgs, GArgsTyEnc, GParams, GenericParamsEnc},
        indirect::{IndirectPredicatesEnc, projection_for_generalized_idx},
        interior_mut::{
            BOUNDARY_IM0_MAP, IM_LEVELS, ImTys, MapUnionEnc, TyInteriorMutUseEnc, im_boundary_maps,
            im0_snap_sources, merge_pairs,
        },
    },
};
use pcg::borrow_pcg::{
    ArgIdxOrResult, FunctionData, FunctionShape, FunctionShapeInput, FunctionShapeNode,
    FunctionShapeOutput, MakeFunctionShapeError, region_projection::Generalized,
    state::BorrowsState, unblock_graph::UnblockGraph,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

#[derive(Clone, Debug)]
pub enum WandEncError {
    Unsupported(String),
}

impl<'vir, E: TaskEncoder> ImpureEncVisitor<'vir, '_, E> {
    pub fn package_wands(
        &mut self,
        final_borrow_state: &BorrowsState<'_, 'vir>,
    ) -> EncodeResult<'vir, Vec<vir::Stmt<'vir>>, E> {
        let mut wand_packages = Vec::new();
        let label = self.new_label("package_post");
        let result = self.local_defs[mir::RETURN_PLACE].impure_snap;
        let result = self.vcx.mk_local_labelled_old_expr(result, label);
        let args = self
            .local_defs
            .args()
            .map(|a| self.vcx.mk_old_expr(a.impure_snap));
        let args = PledgeExpr::pledge_args(result, args);

        for (idx, wand_data) in self.wands.viper_wands().into_iter().enumerate() {
            let Some(wand) =
                self.wands
                    .mk_wand(&wand_data, args, None, None, idx == 0, self.vcx, self.deps)
            else {
                continue;
            };
            let mut package_script = Vec::new();
            for rhs in wand_data.rhs.iter() {
                let ug = UnblockGraph::for_node(
                    mir::Place::from(rhs.mir_local()),
                    final_borrow_state,
                    self.pcg_ctxt(),
                );
                let actions = ug.actions(self.pcg_ctxt()).unwrap();
                let unblock = self.block(|visitor| {
                    visitor.pcs_unblock_actions(final_borrow_state, &actions, Some(label))
                })?;
                package_script.extend(unblock);
            }

            if !wand_data.pledges.is_empty() {
                // Statements in the package script only see resources already
                // in the package state. A resource that is not obtained from
                // the LHS (e.g. an argument the result does not borrow from)
                // is only moved there when consumed, which for the RHS happens
                // after the script. Asserting the RHS resources moves them in
                // early, so that the pledge exhales below can read them.
                let resources = wand_data
                    .rhs
                    .iter()
                    .filter_map(|g| {
                        self.wands.encode_predicates_for_function_shape_node(
                            self.vcx,
                            self.deps,
                            *g,
                            None,
                            |i| args[i],
                        )
                    })
                    .collect::<Vec<_>>();
                package_script.push(self.vcx.mk_assert_stmt(self.vcx.mk_conj(&resources)));
            }

            for EncodedPledge {
                expiry_postcondition,
                ..
            } in &wand_data.pledges
            {
                let span = expiry_postcondition.span();
                self.vcx.with_span(span, |vcx| {
                    vcx.handle_error("exhale.failed:assertion.false", move |_| {
                        Some(vec![PrustiError::verification(
                            "pledge postcondition might not hold",
                            span.into(),
                        )])
                    });
                    package_script.push(vcx.mk_exhale_stmt(expiry_postcondition.expr(args)));
                });
            }
            wand_packages.push(
                self.vcx
                    .mk_package_stmt(wand, self.vcx.alloc_slice(&package_script)),
            );
        }
        Ok(wand_packages)
    }
}

type EncodedPledges<'vir> = Vec<EncodedPledge<'vir>>;

/// Not tied to a caller or callee context. `indirect_pres`, `indirect_posts`,
/// `wand_posts`, and `package_wands` are identity-substituted and intended for
/// use in the callee's own contract; `apply_wands` is for caller use and
/// re-substitutes via a [`WandCallContext`].
#[derive(Clone)]
pub struct WandEncOutput<'vir> {
    /// Information about the corresponding function.
    function_data: FunctionData<'vir>,

    /// The lifetime projections of all arguments to the function.
    inputs: Vec<FunctionShapeInput<Generalized>>,

    /// The lifetime projections of all function outputs (according to the
    /// corresponding [`FunctionShape`]). This *includes* lifetime projections
    /// of nested lifetimes in the function arguments.
    outputs: Vec<FunctionShapeOutput<Generalized>>,

    /// Encoded VIR expressions for the magic wands.
    wands: Vec<WandData<'vir>>,
}

/// Substitution context for instantiating a wand at a call site. When `None`,
/// the wand is encoded using the callee's identity substitution (appropriate
/// when emitting wands inside the function being defined). When `Some`, the
/// wand is re-encoded with the call-site substitutions and the caller's
/// generic parameters, so that placeholders like `Self` or other callee
/// generics are replaced by concrete types from the caller's perspective.
pub type WandCallContext<'vir> = Option<GArgs<'vir>>;

impl<'vir> WandEncOutput<'vir> {
    pub(crate) fn fn_sig(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: WandCallContext<'vir>,
    ) -> ty::FnSig<'vir> {
        match call_ctx {
            // TODO: change pcg's `fn_sig` to take `&[GenericArg]` instead of `GenericArgsRef`
            Some(ctx) => self
                .function_data
                .fn_sig(vcx.tcx(), vcx.tcx().mk_args(ctx.args())),
            None => self.function_data.identity_fn_sig(vcx.tcx()),
        }
    }

    pub(crate) fn g_params(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        call_ctx: WandCallContext<'vir>,
    ) -> GParams<'vir> {
        match call_ctx {
            Some(ctx) => ctx.context(),
            None => GParams::new(
                self.function_data.identity_substs(vcx.tcx()),
                self.function_data.param_env(vcx.tcx()),
                false,
            ),
        }
    }

    /// The (unreified) predicates associated with the given node, or `None` if
    /// there are no resources associated with it.
    #[allow(clippy::type_complexity)]
    fn predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: FunctionShapeNode<Generalized>,
        call_ctx: WandCallContext<'vir>,
    ) -> Option<Vec<vir::ExprGenBool<'vir, vir::ExprSnap<'vir>, vir::ExprKind<'vir>>>> {
        let arg_ty = g.ty(self.fn_sig(vcx, call_ctx));
        let decomp = RustTyDecomposition::from_ty(arg_ty, self.g_params(vcx, call_ctx));
        let region_proj =
            projection_for_generalized_idx(arg_ty, g.region_idx(), decomp, vcx.tcx())?;
        let predicates = deps
            .require_dep::<IndirectPredicatesEnc>(region_proj)
            .unwrap()
            .predicate_applications;
        (!predicates.is_empty()).then_some(predicates)
    }

    fn encode_predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode<Generalized>>,
        call_ctx: WandCallContext<'vir>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> Option<vir::ExprBool<'vir>> {
        use vir::Reify;
        let g = g.into();
        let predicates = self.predicates_for_function_shape_node(vcx, deps, g, call_ctx)?;

        let local = g.mir_local();
        let local_snap = snap(local);
        Some(
            vcx.mk_conj(
                &predicates
                    .iter()
                    .map(|p| p.reify(vcx, local_snap))
                    .collect::<Vec<_>>(),
            ),
        )
    }

    /// The `(owned, shared)` permission-map pairs of the interior-mutable
    /// objects reachable through references in a single function shape node
    /// (collected by the `_IM_N` functions of the types behind those
    /// references), per IM level. Mirrors
    /// [`Self::encode_predicates_for_function_shape_node`], but returns the
    /// `_IM_N` pairs instead of the predicate applications.
    fn interior_mut_pairs_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode<Generalized>>,
        call_ctx: WandCallContext<'vir>,
        snap: vir::ExprSnap<'vir>,
    ) -> [Vec<vir::Expr<'vir, vir::Pair>>; IM_LEVELS] {
        use vir::Reify;
        let g = g.into();
        let fn_sig = self.fn_sig(vcx, call_ctx);
        let arg_ty = g.ty(fn_sig);
        let decomp = RustTyDecomposition::from_ty(arg_ty, self.g_params(vcx, call_ctx));
        let Some(region_proj) =
            projection_for_generalized_idx(arg_ty, g.region_idx(), decomp, vcx.tcx())
        else {
            return [vec![], vec![]];
        };
        let out = deps
            .require_dep::<IndirectPredicatesEnc>(region_proj)
            .unwrap();
        out.interior_mut_pairs
            .map(|ps| ps.iter().map(|p| p.reify(vcx, snap)).collect())
    }

    /// The `(owned, shared)` pairs of the interior-mutable objects reachable
    /// through references in the function's arguments, per IM level, in the
    /// `old` state (i.e. for use in the postcondition). Note that this does
    /// not include the interior-mutable objects owned by the arguments
    /// directly: those are consumed by the function and are not returned to
    /// the caller.
    /// Also returns the `(type, address, snapshot)` sources of the type-level
    /// entries, for the canonical `im0_snap` map of the postcondition
    /// (expanded function-shape entries contribute no source: their objects'
    /// level-0 values are then read as `im_snap_default` — an accepted
    /// incompleteness for partially-blocked reference arguments).
    pub fn interior_mut_post_pairs<E: TaskEncoder>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &MirLocalDefEncOutput<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> (
        [Vec<vir::Expr<'vir, vir::Pair>>; IM_LEVELS],
        Vec<(
            RustTyDecomposition<'vir>,
            vir::ExprRef<'vir>,
            vir::ExprSnap<'vir>,
        )>,
    ) {
        let mut pairs: [Vec<vir::Expr<'vir, vir::Pair>>; IM_LEVELS] = [vec![], vec![]];
        let mut sources = Vec::new();
        // As in `indirect_posts`, inputs blocked by a result lifetime
        // projection are skipped: their permission sits behind the wand until
        // expiry (so their maps cannot even be evaluated here), and their
        // interior-mutable objects are reachable through the result's maps.
        let blocked = self.blocked_inputs();
        // A reference-typed argument none of whose lifetime projections are
        // blocked contributes the pair of its own type's `_IM_N` functions
        // (over the `old` snapshot) instead of the expanded function-shape
        // pairs: this is the exact term shape of the precondition QPs, so the
        // postcondition exhale matches the inhaled maps (near-)syntactically.
        // The expanded pairs express the same set, but proving that requires
        // walking the union/pair structure, which the solver often cannot do
        // within its limits. (This does not apply to by-value arguments:
        // their type-level pair also contains their owned objects, which are
        // consumed by the function.)
        let mut type_level = FxHashSet::default();
        let mut has_blocked = FxHashSet::default();
        for g in self.inputs() {
            if blocked.contains(&g) {
                has_blocked.insert(g.mir_local());
            }
        }
        let fn_sig = self.fn_sig(vcx, None);
        for g in self.inputs() {
            let local = g.mir_local();
            let arg = &local_defs[local];
            let arg_ty = FunctionShapeNode::from(g).ty(fn_sig);
            let shared_ref = matches!(arg_ty.kind(), ty::TyKind::Ref(_, _, ty::Mutability::Not));
            // A blocked input's interior-mutable objects sit behind the wand
            // until expiry — EXCEPT behind a shared reference: sharing is
            // what interior mutability is for, so the caller keeps access
            // while the borrow is live (e.g. reading a `RefCell`'s borrow
            // flag with a guard outstanding). The expiry wand still routes
            // such objects through both of its sides so their values can
            // change at expiry (the count decrement).
            if blocked.contains(&g) && !shared_ref {
                continue;
            }
            // Provably interior-mut-free arguments contribute nothing; they
            // are also skipped in the precondition QPs (see the method
            // encoder), keeping the map terms of both sides aligned.
            if crate::encoders::ty::interior_mut::provably_no_interior_mut(
                vcx.tcx(),
                arg_ty,
                &mut Default::default(),
            ) {
                continue;
            }
            if matches!(arg_ty.kind(), ty::TyKind::Ref(..))
                && (shared_ref || !has_blocked.contains(&local))
            {
                if type_level.insert(local) {
                    // Contributes through the canonical triple form (see
                    // `im_boundary_maps` in the method encoder), not as a
                    // type-level pair expression.
                    deps.require_dep::<TyInteriorMutUseEnc>(arg.ty).unwrap();
                    let snap = vcx.mk_old_expr(arg.impure_snap);
                    sources.push((arg.ty, arg.local_ex, snap));
                }
                continue;
            }
            let snap = vcx.mk_old_expr(arg.impure_snap);
            let ps = self.interior_mut_pairs_for_function_shape_node(vcx, deps, g, None, snap);
            for (level, p) in ps.into_iter().enumerate() {
                pairs[level].extend(p);
            }
        }
        (pairs, sources)
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.inputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_snap
            })
        })
    }

    pub fn indirect_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        // The encoded predicates for the input lifetime projections that are
        // not blocked by any of the result lifetime projections. These will be
        // encoded as part of the postcondition of the function (in contrast,
        // the predicates for the blocked inputs will appear on the right-hand
        // side of a magic wand in the postcondition).
        let unblocked_input_posts = self
            .inputs()
            .filter(|i| !self.blocked_inputs().contains(i))
            .filter_map(|lp| {
                self.encode_predicates_for_function_shape_node(vcx, deps, lp, None, |i| {
                    vcx.mk_old_expr(local_defs[i].impure_snap)
                })
            })
            .collect::<Vec<_>>()
            .into_iter();

        let output_posts = self.outputs().filter_map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, None, |i| {
                local_defs[i].impure_snap
            })
        });
        unblocked_input_posts.chain(output_posts)
    }

    pub fn wand_posts<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        let wand_result =
            vcx.mk_local_decl("wand_result", local_defs[mir::RETURN_PLACE].local_snap.ty());
        let wand_result_expr = vcx.mk_local_ex(wand_result);
        let args = local_defs
            .args()
            .map(|arg| vcx.mk_old_expr(arg.impure_snap));
        let args = PledgeExpr::pledge_args(wand_result_expr, args);

        // TODO: wands for late-bound regions
        self.viper_wands()
            .into_iter()
            .enumerate()
            .filter_map(move |(idx, wand_data)| {
                let wand = self.mk_wand(&wand_data, args, None, None, idx == 0, vcx, deps)?;
                Some(vcx.mk_let_expr(
                    wand_result,
                    local_defs[mir::RETURN_PLACE].impure_snap,
                    vcx.mk_wand_expr(wand),
                ))
            })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::ExprSnap<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
        call_ctx: GArgs<'vir>,
        visitor: &mut ImpureEncVisitor<'vir, '_, E>,
    ) {
        let result = visitor
            .vcx
            .mk_local_labelled_old_expr(arguments[mir::RETURN_PLACE.as_usize()], label_post);
        let args = (1..arguments.len()).map(|l| {
            visitor
                .vcx
                .mk_local_labelled_old_expr(arguments[l], label_pre)
        });
        let args = PledgeExpr::pledge_args(result, args);
        for (idx, wand_data) in self.viper_wands().into_iter().enumerate() {
            let Some(wand) = self.mk_wand(
                &wand_data,
                args,
                Some(label_pre),
                Some(call_ctx),
                idx == 0,
                visitor.vcx,
                visitor.deps,
            ) else {
                continue;
            };
            visitor.stmt(visitor.vcx.mk_apply_stmt(wand));
        }
    }

    /// The interior-mutability QPs (level 0, then level 1 under its
    /// `let`-bound level-0 snapshot) over the given function shape nodes,
    /// for use in a wand side: the pre- and postcondition boundary QPs cover
    /// only the unblocked projections, so the blocked ones' interior-mutable
    /// objects travel through the wand — the caller regains them at expiry,
    /// and an expiry pledge reading interior-mutable state (through a
    /// `#[pure_unstable]` call, whose materialized map requires the QP) can
    /// be evaluated on the right-hand side. The level-1 amounts read the
    /// level-0 state through heap-dependent terms, which Silicon evaluates
    /// when the wand is applied (in conjunct order, so after the level-0 QP
    /// has been produced), not when it is inhaled: they reflect the
    /// post-expiry state, e.g. a `RefCell`'s value share at the count the
    /// pledge re-establishes. This conjunct order also packages.
    fn interior_mut_wand_qp<E: TaskEncoder>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        nodes: impl Iterator<Item = FunctionShapeNode<Generalized>>,
        call_ctx: WandCallContext<'vir>,
        pledge_args: PledgeArgs<'vir>,
        referents_held: bool,
    ) -> Option<vir::ExprBool<'vir>> {
        // All shape DECISIONS (which nodes contribute) are made on the
        // identity signature: the wand in the callee's postcondition and the
        // one reconstructed at a call site must be structurally identical
        // after Viper's substitution, so a node skipped at a concrete
        // instantiation but kept generically (or vice versa) would make the
        // apply fail with `wand.not.found`.
        let identity_sig = self.fn_sig(vcx, None);
        let ctx_sig = self.fn_sig(vcx, call_ctx);
        let identity_params = self.g_params(vcx, None);
        let ctx_params = self.g_params(vcx, call_ctx);
        let mut pairs: [Vec<vir::Expr<'vir, vir::Pair>>; IM_LEVELS] = [vec![], vec![]];
        let mut sources = Vec::new();
        // Whether the sources' level-1 QP is emitted, decided on the
        // identity types (see `im_boundary_maps`).
        let mut level1 = false;
        for g in nodes {
            let snap = pledge_args[g.mir_local()];
            let node_ty = g.ty(identity_sig);
            if crate::encoders::ty::interior_mut::provably_no_interior_mut(
                vcx.tcx(),
                node_ty,
                &mut Default::default(),
            ) {
                continue;
            }
            // A reference node contributes through the canonical `im0_snap`
            // triple (see `im_boundary_maps` in the method encoder), matching
            // the term shape of the boundary QPs that put its permissions in
            // the caller's state. A mutable reference's referent value is
            // read from the heap, which keys the referent's objects: only
            // where the referent is held when the side is evaluated (the
            // right-hand side, inhaled at apply). The path decision is on
            // the identity signature; the expression on the call-context one
            // (its terms substitute cleanly: the reference triples involve
            // no generic casts).
            let heap_read = match node_ty.kind() {
                ty::TyKind::Ref(_, _, ty::Mutability::Not) => true,
                ty::TyKind::Ref(_, _, ty::Mutability::Mut) => referents_held,
                _ => false,
            };
            if heap_read {
                let decomp = RustTyDecomposition::from_ty(g.ty(ctx_sig), ctx_params);
                sources.push((decomp, vcx.mk_null(), snap));
                level1 |= !crate::encoders::ty::interior_mut::provably_no_level1_interior_mut(
                    RustTyDecomposition::from_ty(node_ty, identity_params),
                    &mut Default::default(),
                );
                continue;
            }
            // Other nodes keep the function-shape (generic, `s_Param`-form)
            // pairs: the wand emitted in the callee's postcondition and the
            // wand reconstructed at the caller's apply must be structurally
            // identical after Viper's substitution, which the generic-first
            // shape guarantees (a type-level pair built from the substituted
            // signature encodes concrete-specialized casts and no longer
            // matches — the same lesson as the pledges).
            let ps = self.interior_mut_pairs_for_function_shape_node(vcx, deps, g, call_ctx, snap);
            for (level, ps) in ps.into_iter().enumerate() {
                pairs[level].extend(ps);
            }
        }
        if pairs.iter().all(|ps| ps.is_empty()) && sources.is_empty() {
            return None;
        }
        let tys = ImTys::new(deps);
        let unions = deps.require_dep::<MapUnionEnc>(()).unwrap();
        let maps = im_boundary_maps(deps, &sources, &[], level1).unwrap();
        let [pairs_0, pairs_1] = pairs;
        let extra_0 = (!pairs_0.is_empty()).then(|| merge_pairs(&tys, &unions, pairs_0));
        let has_pairs_1 = !pairs_1.is_empty();
        let extra_1 = has_pairs_1.then(|| merge_pairs(&tys, &unions, pairs_1));
        let mut qps = vec![maps.qp0(vcx, deps, extra_0).unwrap()];
        if let Some(mut qp1) = maps.qp1(vcx, deps, extra_1).unwrap() {
            // The expanded function-shape pair expressions reference the
            // fixed `BOUNDARY_IM0_MAP` name (as in the method contracts).
            if has_pairs_1 {
                let l0_map_decl = vcx.mk_local_decl(BOUNDARY_IM0_MAP, tys.snap_map);
                let l0_map = im0_snap_sources(deps, &sources, &[]).unwrap();
                qp1 = vcx.mk_let_expr(l0_map_decl, l0_map, qp1);
            }
            qps.push(qp1);
        }
        Some(vcx.mk_conj(&qps))
    }

    /// `primary` marks the ONE wand per function that carries the
    /// interior-mutability QPs (they are function-level, so they are
    /// exchanged exactly once per expiry rather than once per coupled edge):
    /// the first of the selected wands (see `select_wands`), so the callee's
    /// postcondition, the package, and every apply site agree on it.
    #[allow(clippy::too_many_arguments)]
    fn mk_wand<E: TaskEncoder>(
        &self,
        wand_data: &WandData<'vir>,
        pledge_args: PledgeArgs<'vir>,
        pledge_old_label: Option<&'vir str>,
        call_ctx: WandCallContext<'vir>,
        primary: bool,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Option<vir::Wand<'vir>> {
        debug_assert!(!wand_data.lhs.is_empty());
        let generics = self.generics_subst(call_ctx, vcx, deps);
        let pledge_expr = |pledge: &PledgeExpr<'vir>| match pledge_old_label {
            Some(label) => {
                vcx.with_local_subst(generics, || pledge.expr_at_label(pledge_args, label))
            }
            None => pledge.expr(pledge_args),
        };
        let rhs = wand_data
            .rhs
            .iter()
            .filter_map(|g| {
                self.encode_predicates_for_function_shape_node(vcx, deps, *g, call_ctx, |i| {
                    pledge_args[i]
                })
            })
            .collect::<Vec<_>>();
        // A wand is a pure transfer of permissions. Only the
        // interior-mutable objects of genuinely BLOCKED inputs travel
        // through it: those behind a mutable reference. The objects behind a
        // shared-reference input are not blocked at all (sharing is what
        // interior mutability is for): the postcondition leaves them with
        // the caller, who keeps them across the apply, so routing them
        // through the wand would let an expiry pledge contradict a value the
        // caller provably still holds. The node selection uses the identity
        // signature (see `interior_mut_wand_qp`).
        let identity_sig = self.fn_sig(vcx, None);
        let shared_ref = |node: FunctionShapeNode<Generalized>| {
            matches!(
                node.ty(identity_sig).kind(),
                ty::TyKind::Ref(_, _, ty::Mutability::Not)
            )
        };
        let rhs_im = primary
            .then(|| {
                self.interior_mut_wand_qp(
                    vcx,
                    deps,
                    wand_data
                        .rhs
                        .iter()
                        .map(|g| FunctionShapeNode::from(*g))
                        .filter(|node| !shared_ref(*node)),
                    call_ctx,
                    pledge_args,
                    true,
                )
            })
            .flatten();
        // The left-hand side carries the interior-mutable objects of the
        // reference-typed results (which the caller reached through the
        // borrow). Non-reference results (e.g. guard structs) are skipped:
        // what they hold stays with the caller. So are the outputs that are
        // nested lifetimes of the inputs (the `'b` of a `&'a mut RefMut<'b,
        // T>` argument): their objects sit behind the blocked referent,
        // which the wand's right-hand side returns.
        let lhs_im_nodes = wand_data
            .lhs
            .iter()
            .copied()
            .filter(|g| matches!(g.base(), ArgIdxOrResult::Result))
            .filter(|g| matches!(g.ty(identity_sig).kind(), ty::TyKind::Ref(..)))
            .collect::<Vec<_>>();
        let lhs_im = primary
            .then(|| {
                self.interior_mut_wand_qp(
                    vcx,
                    deps,
                    lhs_im_nodes.into_iter(),
                    call_ctx,
                    pledge_args,
                    false,
                )
            })
            .flatten();
        let rhs = rhs
            .into_iter()
            .chain(rhs_im)
            .chain(
                wand_data
                    .pledges
                    .iter()
                    .map(|pledge| pledge_expr(&pledge.expiry_postcondition)),
            )
            .collect::<Vec<_>>();
        if rhs.is_empty() {
            // We skip emitting the wand when there is nothing on the RHS, i.e.,
            // nothing would be unblocked by applying this wand, nor are there
            // any pledge postconditions.
            return None;
        }
        let rhs = vcx.mk_conj(&rhs);
        let lhs = wand_data
            .lhs
            .iter()
            .filter_map(|g| {
                self.encode_predicates_for_function_shape_node(vcx, deps, *g, call_ctx, |i| {
                    pledge_args[i]
                })
            })
            .collect::<Vec<_>>();
        let lhs = lhs
            .into_iter()
            .chain(lhs_im)
            .chain(
                wand_data
                    .pledges
                    .iter()
                    .filter_map(|pledge| pledge.expiry_obligation.as_ref().map(pledge_expr)),
            )
            .collect::<Vec<_>>();
        let lhs = vcx.mk_conj(&lhs);
        Some(vcx.mk_wand(lhs, rhs))
    }

    /// The pledges are encoded once, at the callee's identity substitution,
    /// so they refer to the callee's generic parameters. At a call site, these
    /// are replaced by the call's generic arguments, as Viper does for the
    /// callee's postcondition (from which the caller holds the wand).
    fn generics_subst<E: TaskEncoder>(
        &self,
        call_ctx: WandCallContext<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> &'vir FxHashMap<&'vir str, vir::ExprDyn<'vir>> {
        let Some(call_args) = call_ctx else {
            return vcx.alloc(FxHashMap::default());
        };
        let params = deps
            .require_dep::<GenericParamsEnc>(self.g_params(vcx, None))
            .unwrap();
        let args = deps.require_dep::<GArgsTyEnc>(call_args).unwrap();
        let tys = params
            .ty_decls()
            .iter()
            .zip(args.get_ty::<(), !>())
            .map(|(decl, arg)| (decl.name, arg.as_dyn()));
        let consts = params
            .const_decls()
            .iter()
            .zip(args.get_const::<(), !>())
            .map(|(decl, arg)| (decl.name, arg.as_dyn()));
        vcx.alloc(tys.chain(consts).collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct WandEncTask<'tcx> {
    pub data: FunctionData<'tcx>,
}

impl<'tcx> WandEncTask<'tcx> {
    pub fn def_id(&self) -> DefId {
        self.data.def_id()
    }

    pub fn function_shape(
        &self,
        vcx: &vir::VirCtxt<'tcx>,
    ) -> Result<FunctionShape<Generalized>, MakeFunctionShapeError> {
        self.data.shape(vcx.tcx())
    }
}

pub type WandRhsKey = FunctionShapeInput<Generalized>;
pub type WandLhsKey = FunctionShapeNode<Generalized>;

#[derive(Clone, Debug)]
pub struct WandData<'vir> {
    /// Lifetime projections on the right-hand side of the wand. Guaranteed to be
    /// non-empty.
    rhs: Vec<WandRhsKey>,
    /// Lifetime projections on the left-hand side of the wand. Guaranteed to be
    /// non-empty.
    lhs: Vec<WandLhsKey>,
    pledges: EncodedPledges<'vir>,
}

impl<'vir> WandData<'vir> {
    pub fn new(lhs: Vec<WandLhsKey>, rhs: Vec<WandRhsKey>, pledges: EncodedPledges<'vir>) -> Self {
        debug_assert!(!lhs.is_empty());
        debug_assert!(!rhs.is_empty());
        Self { rhs, lhs, pledges }
    }
}

impl TaskEncoder for WandEnc {
    task_encoder::encoder_cache!(WandEnc);

    type TaskDescription<'vir> = WandEncTask<'vir>;

    type TaskKey<'vir> = WandEncTask<'vir>;

    type OutputFullDependency<'vir> = WandEncOutput<'vir>;

    type EncodingError = WandEncError;

    const ENCODER_NAME: &'static str = "wand encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        task.clone()
    }

    fn describe_error(error: Self::EncodingError) -> String {
        match error {
            WandEncError::Unsupported(message) => message,
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(task_key.clone(), ())?;
        vir::with_vcx(|vcx| {
            let def_id = task_key.def_id();

            let shape = task_key.function_shape(vcx).map_err(|e| {
                EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!("function shape: {e:?}")),
                    None,
                )
            })?;

            let coupled_edges = shape.coupled_edges();
            let edges: FxHashSet<_> = shape.edges().map(|e| (e.input(), e.output())).collect();

            let (inputs, outputs) = shape.take_inputs_and_outputs();
            let spec = deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::Impure))?;
            if coupled_edges.is_empty() {
                assert!(spec.pledges.is_empty());
                return Ok((
                    (),
                    WandEncOutput {
                        function_data: task_key.data,
                        inputs,
                        outputs,
                        wands: vec![],
                    },
                ));
            }
            let pledges = spec.pledges;
            let wands: Vec<WandData<'vir>> = coupled_edges
                .into_iter()
                .filter_map(|hyper_edge| {
                    let (sources, mut targets) = hyper_edge.into_tuple();
                    // We don't want to emit an identity wand, like P --* P. This can happen when
                    // PCG returns self-edges, like for fn(x: &'a mut &'b i32) where 'b is in
                    // invariant position and we therefore have an edge x|'b -> x|'b.
                    // Currently, these edges also prevent us from emitting indirect postconditions.
                    // TODO: we might want to emit these identity wands in the future to attach functional
                    // specifications to them. We still need to emit the resources on the wand's LHS.
                    let mut sources_as_nodes = sources
                        .iter()
                        .map(|&s| s.to_function_shape_node())
                        .collect::<Vec<_>>();
                    sources_as_nodes.sort();
                    targets.sort();
                    if sources_as_nodes == targets {
                        return None;
                    }
                    Some(WandData::new(targets, sources, pledges.clone()))
                })
                .collect();
            let mut output: WandEncOutput<'vir> = WandEncOutput {
                function_data: task_key.data,
                inputs,
                outputs,
                wands: Vec::new(),
            };
            output.wands = output
                .select_wands(wands, !pledges.is_empty(), &edges, vcx, deps)
                .map_err(|err| EncodeFullError::EncodingError(err, None))?;
            Ok(((), output))
        })
    }
}

impl<'vir> WandEncOutput<'vir> {
    /// Selects the wands to emit among those of the coupled edges, rejecting
    /// the shapes that cannot be encoded precisely.
    fn select_wands<E: TaskEncoder>(
        &self,
        wands: Vec<WandData<'vir>>,
        has_pledges: bool,
        edges: &FxHashSet<(WandRhsKey, WandLhsKey)>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> Result<Vec<WandData<'vir>>, WandEncError> {
        let mut has_resources = |g: FunctionShapeNode<Generalized>| {
            self.predicates_for_function_shape_node(vcx, deps, g, None)
                .is_some()
        };
        // A wand is only needed if it gives back a resource, or to carry the
        // pledges if none does (e.g. for shared references).
        let (mut wands, resourceless): (Vec<_>, Vec<_>) = wands
            .into_iter()
            .partition(|wand_data| wand_data.rhs.iter().any(|g| has_resources((*g).into())));
        // A wand gives back its sources only once all of its targets have
        // expired. That matches the signature only if each source with
        // resources flows into each target with resources.
        for wand_data in &wands {
            let sources = wand_data
                .rhs
                .iter()
                .filter(|g| has_resources((**g).into()))
                .collect::<Vec<_>>();
            let targets = wand_data
                .lhs
                .iter()
                .filter(|g| has_resources(**g))
                .collect::<Vec<_>>();
            let precise = sources.iter().all(|source| {
                let mut targets = targets.iter();
                targets.all(|target| edges.contains(&(**source, **target)))
            });
            if !precise {
                return Err(WandEncError::Unsupported(
                    "borrows in the result that expire separately but depend on a common \
                     argument are not supported"
                        .to_string(),
                ));
            }
        }
        if has_pledges {
            if wands.is_empty() {
                wands.extend(resourceless.into_iter().take(1));
            } else if wands.len() > 1 {
                // It is unclear which expiry the pledges refer to.
                return Err(WandEncError::Unsupported(
                    "pledges on a function whose result contains borrows that expire \
                     separately are not supported"
                        .to_string(),
                ));
            }
        }
        Ok(wands)
    }

    pub fn viper_wands(&self) -> Vec<WandData<'vir>> {
        self.wands.clone()
    }

    /// All lifetime projections in the arguments that are blocked by any of the
    /// lifetime projections in the function's result.
    pub fn blocked_inputs(&self) -> FxHashSet<FunctionShapeInput<Generalized>> {
        self.wands
            .iter()
            .flat_map(|wand| wand.rhs.iter().copied())
            .collect()
    }

    pub fn inputs(&self) -> impl Iterator<Item = FunctionShapeInput<Generalized>> + '_ {
        self.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = FunctionShapeOutput<Generalized>> + '_ {
        self.outputs.iter().copied()
    }
}
