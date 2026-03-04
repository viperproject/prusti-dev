use crate::encoders::{
    ImpureEncVisitor, MirLocalDefEncOutput, MirSpecEnc,
    pure::spec::{EncodedPledge, MirSpecEncMode, PledgeArgs, PledgeExpr},
    ty::{RustTyDecomposition, generics::GParams, indirect::IndirectPredicatesEnc},
};
use pcg::borrow_pcg::{
    FunctionData, FunctionShape, FunctionShapeInput, FunctionShapeNode, FunctionShapeOutput,
    MakeFunctionShapeError, state::BorrowsState, unblock_graph::UnblockGraph,
};
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::HasType;

/// Encodes the magic wands given a function signature.
pub struct WandEnc;

#[derive(Clone, Debug)]
pub enum WandEncError {
    Unsupported(#[allow(dead_code)] String),
}

impl<'vir, E: TaskEncoder> ImpureEncVisitor<'vir, '_, E> {
    pub fn package_wands(
        &mut self,
        final_borrow_state: &BorrowsState<'_, 'vir>,
    ) -> Result<Vec<vir::Stmt<'vir>>, EncodeFullError<'vir, E>> {
        let mut wand_packages = Vec::new();
        let label = self.new_label("package_post");
        let result = self.local_defs.locals[mir::RETURN_PLACE].impure_snap;
        let result = self.vcx.mk_local_labelled_old_expr(result, label);
        let args = self
            .local_defs
            .args()
            .map(|a| self.vcx.mk_old_expr(a.impure_snap));
        let args = PledgeExpr::pledge_args(result, args);

        for wand_data in self.wands.viper_wands() {
            let wand = self.wands.mk_wand(&wand_data, args, self.vcx, self.deps);
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

#[derive(Clone)]
pub struct WandEncOutput<'vir> {
    /// Information about the corresponding function.
    function_data: FunctionData<'vir>,

    /// The lifetime projections of all arguments to the function.
    inputs: Vec<FunctionShapeInput>,

    /// The lifetime projections of all function outputs (according to the
    /// corresponding [`FunctionShape`]). This *includes* lifetime projections
    /// of nested lifetimes in the function arguments.
    outputs: Vec<FunctionShapeOutput>,

    /// Encoded VIR expressions for the magic wands.
    wands: Vec<WandData<'vir>>,
}

impl<'vir> WandEncOutput<'vir> {
    pub(crate) fn fn_sig(&self, vcx: &'vir vir::VirCtxt<'vir>) -> ty::FnSig<'vir> {
        self.function_data.instantiated_fn_sig(vcx.tcx())
    }

    pub(crate) fn g_params(&self, vcx: &'vir vir::VirCtxt<'vir>) -> GParams<'vir> {
        GParams::new(
            self.function_data.substs(),
            self.function_data.param_env(vcx.tcx()),
            false,
        )
    }

    fn encode_predicates_for_function_shape_node(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, impl TaskEncoder>,
        g: impl Into<FunctionShapeNode>,
        mut snap: impl FnMut(mir::Local) -> vir::ExprSnap<'vir>,
    ) -> vir::ExprBool<'vir> {
        use vir::Reify;
        let g = g.into();
        let fn_sig = self.fn_sig(vcx);
        let ty = RustTyDecomposition::from_ty(g.ty(fn_sig), self.g_params(vcx));
        let predicates = deps
            .require_dep::<IndirectPredicatesEnc>(g.with_base(ty))
            .unwrap()
            .predicate_applications;

        let local = g.mir_local();
        let local_snap = snap(local);
        vcx.mk_conj(
            vcx.alloc_slice(
                &predicates
                    .iter()
                    .map(|p| p.reify(vcx, local_snap))
                    .collect::<Vec<_>>(),
            ),
        )
    }

    pub fn indirect_pres<'a, E: TaskEncoder>(
        &'a self,
        vcx: &'vir vir::VirCtxt<'vir>,
        local_defs: &'a MirLocalDefEncOutput<'vir>,
        deps: &'a mut TaskEncoderDependencies<'vir, E>,
    ) -> impl Iterator<Item = vir::ExprBool<'vir>> + 'a {
        self.inputs().map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, |i| {
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
            .map(|lp| {
                self.encode_predicates_for_function_shape_node(vcx, deps, lp, |i| {
                    vcx.mk_old_expr(local_defs[i].impure_snap)
                })
            })
            .collect::<Vec<_>>()
            .into_iter();

        let output_posts = self.outputs().map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, g, |i| {
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
        self.viper_wands().into_iter().map(move |wand_data| {
            let wand = self.mk_wand(&wand_data, args, vcx, deps);
            vcx.mk_let_expr(
                wand_result,
                local_defs[mir::RETURN_PLACE].impure_snap,
                vcx.mk_wand_expr(wand),
            )
        })
    }

    pub fn apply_wands<E: TaskEncoder>(
        &self,
        arguments: &[vir::ExprSnap<'vir>],
        label_pre: &'vir str,
        label_post: &'vir str,
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
        for wand_data in self.viper_wands() {
            let wand = self.mk_wand(&wand_data, args, visitor.vcx, visitor.deps);
            visitor.stmt(visitor.vcx.mk_apply_stmt(wand));
        }
    }

    fn mk_wand<'a, E: TaskEncoder>(
        &'a self,
        wand_data: &WandData<'vir>,
        pledge_args: PledgeArgs<'vir>,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, E>,
    ) -> vir::Wand<'vir> {
        debug_assert!(!wand_data.lhs.is_empty());
        let rhs = wand_data.rhs.iter().map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, *g, |i| pledge_args[i])
        });
        let rhs = rhs.chain(
            wand_data
                .pledges
                .iter()
                .map(|pledge| pledge.expiry_postcondition.expr(pledge_args)),
        );
        let rhs = vcx.mk_conj(vcx.alloc_slice(&rhs.collect::<Vec<_>>()));
        let lhs = wand_data.lhs.iter().map(|g| {
            self.encode_predicates_for_function_shape_node(vcx, deps, *g, |i| pledge_args[i])
        });
        let lhs = lhs.chain(
            wand_data
                .pledges
                .iter()
                .filter_map(|pledge| pledge.expiry_obligation)
                .map(|expr| expr.expr(pledge_args)),
        );
        let lhs = vcx.mk_conj(vcx.alloc_slice(&lhs.collect::<Vec<_>>()));
        vcx.mk_wand(lhs, rhs)
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
    ) -> Result<FunctionShape, MakeFunctionShapeError> {
        self.data.shape(vcx.tcx())
    }
}

pub type WandRhsKey = FunctionShapeInput;
pub type WandLhsKey = FunctionShapeNode;

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

            let coupled_edges = shape.coupled_edges().map_err(|e| {
                EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!("coupled edges: {e:?}")),
                    None,
                )
            })?;

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
            if pledges.len() > 1 && coupled_edges.len() > 1 {
                return Err(EncodeFullError::EncodingError(
                    WandEncError::Unsupported(format!(
                        "multiple pledges: {pledges:?}, coupled edges: {coupled_edges:?}"
                    )),
                    None,
                ));
            }
            let wands: Vec<WandData<'vir>> = coupled_edges
                .into_iter()
                .map(|hyper_edge| {
                    let (sources, targets) = hyper_edge.into_tuple();
                    WandData::new(targets, sources, pledges.clone())
                })
                .collect();
            let output: WandEncOutput<'vir> = WandEncOutput {
                function_data: task_key.data,
                inputs,
                outputs,
                wands,
            };
            Ok(((), output))
        })
    }
}

impl<'vir> WandEncOutput<'vir> {
    pub fn viper_wands(&self) -> Vec<WandData<'vir>> {
        self.wands.clone()
    }

    /// All lifetime projections in the arguments that are blocked by any of the
    /// lifetime projections in the function's result.
    pub fn blocked_inputs(&self) -> FxHashSet<FunctionShapeInput> {
        self.wands
            .iter()
            .flat_map(|wand| wand.rhs.iter().copied())
            .collect()
    }

    pub fn inputs(&self) -> impl Iterator<Item = FunctionShapeInput> + '_ {
        self.inputs.iter().copied()
    }

    pub fn outputs(&self) -> impl Iterator<Item = FunctionShapeOutput> + '_ {
        self.outputs.iter().copied()
    }
}
