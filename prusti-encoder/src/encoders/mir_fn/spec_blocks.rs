use std::collections::VecDeque;

use pcg::r#loop::{LoopAnalysis, LoopId};
use prusti_interface::{PrustiError, environment::EnvQuery, utils::has_prusti_attr};
use prusti_rustc_interface::{
    data_structures::{
        fx::{FxHashMap, FxHashSet},
        graph::dominators::Dominators,
    },
    hir,
    middle::mir::{self, BasicBlock},
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::mir_fn::RustSignature;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpecBlockKind {
    LoopInvariant,
    Assert,
    Assume,
    Refute,
}

/// A `ghost!` block, i.e. the `if false { ghost_call(&closure, body) } else {
/// ghost_erased() }` expansion. The encoders jump into the ghost arm (where
/// the body is evaluated inline, ending in the `ghost_call` terminator) and
/// skip the runtime `ghost_erased` stand-in arm.
#[derive(Clone, Copy, Debug)]
pub struct GhostBlock {
    /// The entry block of the ghost arm.
    pub arm_block: BasicBlock,
    /// The block containing the (skipped) runtime `ghost_erased()` call.
    pub erased_block: BasicBlock,
}

/// The `ghost!` blocks of a MIR body (see [`GhostBlock`]). Unlike the full
/// [`SpecBlocks`], this needs no PCG analysis, so the pure encoder can use
/// the same detection.
#[derive(Clone, Default)]
pub struct GhostBlocks {
    /// Ghost blocks, keyed by the block whose `if false` switch guards them.
    pub switches: FxHashMap<BasicBlock, GhostBlock>,
    /// The blocks of all ghost arms (the inline ghost bodies): spec-only
    /// `prusti_contracts` builtins are allowed there.
    pub code: FxHashSet<BasicBlock>,
}

impl GhostBlocks {
    /// Determine the ghost blocks of the given MIR body. A ghost block is
    /// recognized by its (single-block) runtime stand-in arm calling
    /// `ghost_erased`: the sibling arm of the guarding `if false` switch is
    /// the ghost arm, holding the inline ghost body up to its `ghost_call`
    /// terminator.
    pub fn new<'vir>(def_id: DefId, body: &mir::Body<'vir>) -> Self {
        let visitor = SpecVisitor::run(def_id, body);
        Self::from_erased(body, visitor.erased_blocks)
    }

    /// Builds the ghost blocks from the blocks of the runtime `ghost_erased`
    /// stand-in arms (as collected by [SpecVisitor]).
    fn from_erased<'vir>(
        body: &mir::Body<'vir>,
        erased_blocks: impl IntoIterator<Item = BasicBlock>,
    ) -> Self {
        let mut ghost = GhostBlocks::default();
        for block in erased_blocks {
            ghost.visit_erased(body, block);
        }
        ghost
    }

    /// Records the ghost block whose runtime stand-in arm is `erased_block`.
    fn visit_erased(&mut self, body: &mir::Body<'_>, erased_block: BasicBlock) {
        let switch_block = get_single_predecessor(&body.basic_blocks.predecessors()[erased_block]);
        let mir::TerminatorKind::SwitchInt { targets, .. } = &body[switch_block].terminator().kind
        else {
            unreachable!("malformed ghost block: `ghost_erased` arm not guarded by a switch");
        };
        let arm_block = get_sibling(targets, erased_block);
        self.switches.insert(
            switch_block,
            GhostBlock {
                arm_block,
                erased_block,
            },
        );

        // The ghost arm's blocks (the inline ghost body).
        dominated_blocks(body, arm_block, &mut self.code);
    }
}

/// Returns the other target of a two-armed switch.
fn get_sibling(targets: &mir::SwitchTargets, arm_block: BasicBlock) -> BasicBlock {
    let mut siblings = targets
        .all_targets()
        .iter()
        .copied()
        .filter(|target| *target != arm_block);
    let sibling = siblings
        .next()
        .expect("malformed spec-only arm: no sibling arm");
    assert!(
        siblings.next().is_none(),
        "malformed spec-only arm: expected a two-armed switch"
    );
    sibling
}

/// Collects the arm's blocks into `out`: everything reachable from (and
/// still dominated by) the arm entry. The dominance requirement keeps blocks
/// shared with live code out (the join both arms continue to, and cleanup
/// blocks that calls outside the arm also unwind to).
fn dominated_blocks(body: &mir::Body<'_>, arm_entry: BasicBlock, out: &mut FxHashSet<BasicBlock>) {
    let doms = body.basic_blocks.dominators();
    let mut queue = vec![arm_entry];
    while let Some(block) = queue.pop() {
        if !doms.dominates(arm_entry, block) || !out.insert(block) {
            continue;
        }
        queue.extend(body.basic_blocks[block].terminator().successors());
    }
}

/// The specification-only arms of a MIR body, i.e. the `if false { .. }`
/// expansions of our macros: the `spec_block(..)` arms of `prusti_assert!`
/// and friends, the `return closure_spec_*(..)` marker arms of `closure!`,
/// and the runtime `ghost_erased()` stand-in arms of `ghost!`. The arms are
/// invisible in the encoding: each guarding switch is encoded as an
/// unconditional jump to the live target (the continuation, or the inline
/// ghost body), the arm's blocks are never encoded, and neither are the
/// [spec-only locals](Self::spec_only_locals) nor the (constant)
/// assignments to them.
#[derive(Clone, Default)]
pub struct SpecArms {
    /// The live target, keyed by the block whose `if false` switch guards
    /// a spec-only arm.
    pub switches: FxHashMap<BasicBlock, BasicBlock>,
    /// The blocks of all spec-only arms.
    pub blocks: FxHashSet<BasicBlock>,
    /// The locals only serving the arms: those assigned within the arms,
    /// plus those with no encoded use at all. The latter covers the
    /// [scaffolding](Self::scaffolding) (whose stores are skipped) and the
    /// `!` temps of the `closure!` arms' `return` expressions (mentioned
    /// nowhere). Neither their declarations (and hence types) nor the
    /// assignments to them are encoded.
    pub spec_only_locals: FxHashSet<mir::Local>,
    /// The arms' scaffolding locals, each identified by its structural
    /// anchor: the switch discriminants (the operands of the switches
    /// encoded as gotos; their `const false` stores are their only encodable
    /// mention), the unit values of the arms' `if` statements (stored
    /// `const ()` in the live continuations, kept only when nothing else
    /// uses them — a live unit local in the same block, e.g. a unit
    /// `result` binding, is not scaffolding) and the `PhantomData` binding
    /// tying the `closure!` marker types together (the markers' second
    /// argument, reaching them through an arm-local copy; read outside the
    /// arms only by `FakeRead`). Stores to these locals are not encoded.
    scaffolding: FxHashSet<mir::Local>,
}

impl SpecArms {
    fn new(
        body: &mir::Body<'_>,
        ghost: &GhostBlocks,
        marker_blocks: impl IntoIterator<Item = BasicBlock>,
        phantom_operands: impl IntoIterator<Item = mir::Local>,
    ) -> Self {
        use mir::visit::Visitor;
        let mut arms = Self::default();
        let mut unit_candidates = FxHashSet::default();
        for block in marker_blocks {
            arms.visit_marker(body, block, &mut unit_candidates);
        }
        for (switch_block, ghost_block) in &ghost.switches {
            arms.visit_ghost(body, *switch_block, *ghost_block);
        }
        if arms.switches.is_empty() {
            return arms;
        }

        // The markers receive the `PhantomData` binding through an
        // arm-local copy (`_t = copy _phantom; closure_spec_*(.., move _t)`);
        // resolve the operand back to the binding.
        for operand in phantom_operands {
            let root = arms
                .blocks
                .iter()
                .flat_map(|block| &body[*block].statements)
                .find_map(|stmt| {
                    let mir::StatementKind::Assign(box (dest, rvalue)) = &stmt.kind else {
                        return None;
                    };
                    if dest.as_local() != Some(operand) {
                        return None;
                    }
                    let (mir::Rvalue::Use(mir::Operand::Copy(source))
                    | mir::Rvalue::Use(mir::Operand::Move(source))) = rvalue
                    else {
                        return None;
                    };
                    source.as_local()
                });
            arms.scaffolding.insert(root.unwrap_or(operand));
        }

        // The locals assigned within the arms. The `closure!` markers'
        // `return` writes the closure's return place inside the arm, and a
        // `ghost_erased` stand-in arm writes the same destination as its
        // (encoded) ghost arm; both stay live.
        for block in &arms.blocks {
            for statement in &body[*block].statements {
                if let mir::StatementKind::Assign(box (dest, _)) = &statement.kind {
                    arms.spec_only_locals.extend(dest.as_local());
                }
            }
            if let mir::TerminatorKind::Call { destination, .. } = &body[*block].terminator().kind {
                arms.spec_only_locals.extend(destination.as_local());
            }
        }
        arms.spec_only_locals.remove(&mir::RETURN_PLACE);
        for ghost_block in ghost.switches.values() {
            if let mir::TerminatorKind::Call { destination, .. } =
                &body[ghost_block.erased_block].terminator().kind
                && let Some(local) = destination.as_local()
            {
                arms.spec_only_locals.remove(&local);
            }
        }

        let mut collector = UsedLocals {
            arms: &arms,
            unit_candidates: &unit_candidates,
            used: Default::default(),
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            // Cleanup blocks are emitted as dummy blocks, so their mentions
            // (e.g. `Drop`s of arm temps) are not encoded uses.
            if !arms.blocks.contains(&block) && !data.is_cleanup {
                collector.visit_basic_block_data(block, data);
            }
        }
        let used = collector.used;

        // Unit if-temp candidates with an encoded use are real locals (e.g.
        // a unit `result` binding stored in the same block); only the rest
        // are scaffolding. Skipping the candidates' stores above is sound
        // either way: a unit constant store mentions no other local.
        arms.scaffolding.extend(
            unit_candidates
                .into_iter()
                .filter(|local| !used.contains(local)),
        );

        // Sanity check: nothing encoded outside the arms may use an
        // arm-assigned or scaffolding local.
        assert!(
            arms.spec_only_locals.is_disjoint(&used),
            "spec-only arm locals leak into encoded code: {:?}",
            arms.spec_only_locals
                .intersection(&used)
                .collect::<Vec<_>>()
        );
        assert!(
            arms.scaffolding.is_disjoint(&used),
            "spec-only arm scaffolding locals leak into encoded code: {:?}",
            arms.scaffolding.intersection(&used).collect::<Vec<_>>()
        );

        // The locals without any encoded use.
        let unused = (body.arg_count + 1..body.local_decls.len())
            .map(mir::Local::from)
            .filter(|local| !used.contains(local))
            .collect::<Vec<_>>();
        arms.spec_only_locals.extend(unused);
        arms
    }

    /// Records the spec-only arm containing the given `spec_block` or
    /// `closure_spec_*` call.
    fn visit_marker(
        &mut self,
        body: &mir::Body<'_>,
        marker_block: BasicBlock,
        unit_candidates: &mut FxHashSet<mir::Local>,
    ) {
        // Walk up the single-predecessor chain to the guarding `if false`
        // switch; the chain block below it is the arm entry.
        let mut arm_entry = marker_block;
        let (switch_block, discr, targets) = loop {
            let pred = get_single_predecessor(&body.basic_blocks.predecessors()[arm_entry]);
            if let mir::TerminatorKind::SwitchInt { discr, targets } = &body[pred].terminator().kind
            {
                break (pred, discr, targets);
            }
            arm_entry = pred;
        };
        let live_target = get_sibling(targets, arm_entry);
        self.switches.insert(switch_block, live_target);

        // The switch is encoded as a goto, so its discriminant is never read.
        if let Some(local) = discr.place().and_then(|place| place.as_local()) {
            self.scaffolding.insert(local);
        }
        // The unit value the arm's `if` statement stores in the live
        // continuation; only a candidate, since the block may also store
        // live unit locals (e.g. a unit `result` binding).
        for statement in &body[live_target].statements {
            let mir::StatementKind::Assign(box (dest, rvalue)) = &statement.kind else {
                continue;
            };
            let mir::Rvalue::Use(mir::Operand::Constant(constant)) = rvalue else {
                continue;
            };
            if constant.ty().is_unit() {
                unit_candidates.extend(dest.as_local());
            }
        }

        dominated_blocks(body, arm_entry, &mut self.blocks);
    }

    /// Records a `ghost!` block's runtime stand-in arm: the switch jumps
    /// into the ghost arm (the inline ghost body, which is encoded), only
    /// the single-block `ghost_erased` arm is skipped. Unlike the `if
    /// false` statements of the other arms, `ghost!` expands to an
    /// `if/else` expression, so there are no unit if-temps to anchor.
    fn visit_ghost(&mut self, body: &mir::Body<'_>, switch_block: BasicBlock, ghost: GhostBlock) {
        self.switches.insert(switch_block, ghost.arm_block);
        let mir::TerminatorKind::SwitchInt { discr, .. } = &body[switch_block].terminator().kind
        else {
            unreachable!();
        };
        if let Some(local) = discr.place().and_then(|place| place.as_local()) {
            self.scaffolding.insert(local);
        }
        dominated_blocks(body, ghost.erased_block, &mut self.blocks);
    }
}

#[derive(Debug)]
pub struct LoopSpec {
    pub loop_id: LoopId,

    /// Loop head as identified by the PCG.
    #[allow(dead_code)]
    pub original_head_block: BasicBlock,

    /// Loop head as identified by Prusti, i.e., the body invariant, or the
    /// original loop head if no body invariant is present.
    pub head_block: BasicBlock,

    pub invariants: Vec<(BasicBlock, Span)>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpecBlock {
    pub attached_to: BasicBlock,
    pub block: BasicBlock,
    pub kind: SpecBlockKind,
    pub span: Span,
}

/// Contains information about the spec-only blocks in a given MIR body.
#[derive(Default)]
pub struct SpecBlocks {
    /// Maps specifications to basic blocks.
    pub specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    /// Set of loop specifications, keyed by loop heads.
    pub loop_specs: FxHashMap<BasicBlock, LoopSpec>,
    /// Maps loop IDs (as identified by the PCG loop analysis) to their loop
    /// heads.
    pub loop_head_at: FxHashMap<LoopId, BasicBlock>,
    /// The `ghost!` blocks of the body.
    pub ghost: GhostBlocks,
    /// The specification-only arms of the body.
    pub spec_arms: SpecArms,
}

/// The body-derived part of [SpecBlocks], independent of the (PCG) loop
/// analysis. Memoized per `DefId` by [SpecBlocksEnc] so the spec-arm
/// analysis runs once per body.
#[derive(Clone, Default)]
pub struct SpecBlocksBase {
    /// Maps specifications to basic blocks.
    pub specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    /// The `ghost!` blocks of the body.
    pub ghost: GhostBlocks,
    /// The specification-only arms of the body.
    pub spec_arms: SpecArms,
}

impl SpecBlocksBase {
    /// Determine the spec-only blocks for the given MIR body. Spec-only blocks
    /// are ones which consists of *only* a closure assignment of a closure
    /// marked with the Prusti spec-only attribute. For each spec-only block we
    /// determine which non-spec block it is attached to.
    fn new(def_id: DefId, body: &mir::Body<'_>) -> Self {
        let mut visitor = SpecVisitor::run(def_id, body);

        let ghost = GhostBlocks::from_erased(body, std::mem::take(&mut visitor.erased_blocks));
        let spec_arms = SpecArms::new(
            body,
            &ghost,
            std::mem::take(&mut visitor.closure_marker_blocks)
                .into_iter()
                .chain(visitor.spec_blocks.iter().copied()),
            std::mem::take(&mut visitor.phantom_operands),
        );

        for specified_blocks in visitor.specs_for.values() {
            for spec_block in specified_blocks {
                // If this assertion ever fails, then consecutive spec blocks
                // are actually consecutive blocks in the CFG. If this happens,
                // we need to keep walking up the predecessors for each spec
                // block until we find a non-spec block.
                assert!(!visitor.spec_blocks.contains(&spec_block.attached_to));
            }
        }

        Self {
            specs_for: visitor.specs_for,
            ghost,
            spec_arms,
        }
    }
}

/// Memoizes [SpecBlocksBase] per `DefId`; required by both `MethodEnc` (for
/// the full [SpecBlocks]) and `MirLocalDefEnc` (for the spec-only locals).
pub struct SpecBlocksEnc;

impl TaskEncoder for SpecBlocksEnc {
    task_encoder::encoder_cache!(SpecBlocksEnc);
    const ENCODER_NAME: &'static str = "spec blocks encoder";

    type TaskDescription<'vir> = DefId;
    type OutputFullDependency<'vir> = SpecBlocksBase;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let def_id = *task_key;
        let data = match crate::encoders::impure_body(def_id) {
            Some(body) => SpecBlocksBase::new(def_id, &body),
            None => SpecBlocksBase::default(),
        };
        Ok(((), data))
    }
}

impl SpecBlocks {
    /// Associates the specs of `base` with the loops of the body.
    pub fn new(base: SpecBlocksBase, body: &mir::Body<'_>, loop_analysis: &LoopAnalysis) -> Self {
        // Associate loop invariants with loop IDs (or report errors for ones
        // that are outside of loops).
        let mut loop_invariant_blocks: FxHashMap<LoopId, Vec<&SpecBlock>> = Default::default();
        for specified_blocks in base.specs_for.values() {
            for spec_block in specified_blocks {
                let SpecBlockKind::LoopInvariant = spec_block.kind else {
                    continue;
                };

                // Body invariants must only be placed inside loops.
                let Some(loop_id) = loop_analysis.innermost_loop(spec_block.block) else {
                    vir::with_vcx(|vcx| {
                        vcx.emit_early_error(PrustiError::incorrect(
                            "`body_invariant!` annotations must be placed inside loop bodies"
                                .to_string(),
                            spec_block.span.into(),
                        ));
                    });
                    continue;
                };

                loop_invariant_blocks
                    .entry(loop_id)
                    .or_default()
                    .push(spec_block);
            }
        }

        let doms = body.basic_blocks.dominators();
        let loop_specs: FxHashMap<LoopId, LoopSpec> = loop_analysis
            .all_loops()
            .map(|loop_id| {
                let original_head_block = loop_analysis[loop_id];
                if let Some(spec_blocks) = loop_invariant_blocks.remove(&loop_id) {
                    match Self::body_invariant_analysis(
                        &base,
                        body,
                        doms,
                        loop_analysis,
                        loop_id,
                        original_head_block,
                        spec_blocks,
                    ) {
                        Ok(spec) => return spec,
                        Err(error) => vir::with_vcx(|vcx| vcx.emit_early_error(error)),
                    }
                }
                // For any loop that is not specified with a body invariant (or
                // where the body invariants are invalid), we default to the
                // loop head being at the loop head identified by the PCG, with
                // no specs.
                LoopSpec {
                    loop_id,
                    head_block: original_head_block,
                    original_head_block,
                    invariants: Vec::new(),
                }
            })
            .map(|spec| (spec.loop_id, spec))
            .collect();

        let loop_head_at = loop_specs
            .iter()
            .map(|(loop_id, spec)| (*loop_id, spec.head_block))
            .collect();
        let loop_specs = loop_specs
            .into_values()
            .map(|spec| (spec.head_block, spec))
            .collect();
        Self {
            specs_for: base.specs_for,
            loop_specs,
            loop_head_at,
            ghost: base.ghost,
            spec_arms: base.spec_arms,
        }
    }

    /// Determine the loop specs (body invariants and invariant block) for the
    /// given loop; an error is returned if the invariants are not well-formed:
    /// they must be reachable unconditionally within a loop iteration, and if
    /// there are multiple, they must be consecutive and not interrupted by
    /// (non-spec) statements.
    fn body_invariant_analysis(
        base: &SpecBlocksBase,
        body: &mir::Body<'_>,
        doms: &Dominators<mir::BasicBlock>,
        loop_analysis: &LoopAnalysis,
        loop_id: LoopId,
        original_head_block: mir::BasicBlock,
        mut spec_blocks: Vec<&SpecBlock>,
    ) -> Result<LoopSpec, PrustiError> {
        assert!(!spec_blocks.is_empty());

        // Sort by domination, if possible.
        let mut can_sort = true;
        spec_blocks.sort_by(|a, b| {
            if doms.dominates(a.attached_to, b.attached_to) {
                std::cmp::Ordering::Less
            } else if doms.dominates(b.attached_to, a.attached_to) {
                std::cmp::Ordering::Greater
            } else {
                can_sort = false;
                std::cmp::Ordering::Equal
            }
        });

        // If we cannot sort by domination, then there are some body invariants
        // that are not on the same control-flow path; report an error (with
        // all the body invariant spans).
        // TODO: should be redundant because of the more specific checks later
        if !can_sort {
            return Err(PrustiError::incorrect(
                "multiple `body_invariant!` annotations must be placed consecutively".to_string(),
                spec_blocks
                    .iter()
                    .map(|spec_block| spec_block.span)
                    .collect::<Vec<_>>()
                    .into(),
            ));
        }

        // Next, we walk the blocks of the loop, starting from the loop head,
        // to find which body invariant blocks are reachable from the head.
        let mut queue = VecDeque::new();
        let mut explored: FxHashSet<BasicBlock> = Default::default();
        let mut invariants_reached: Vec<&SpecBlock> = Default::default();

        queue.push_back(original_head_block);
        while let Some(block) = queue.pop_front() {
            // stop exploring if we already saw this block, if we stepped out
            // of the current loop, or if the block is a cleanup block
            if !explored.insert(block)
                || !loop_analysis.in_loop(block, loop_id)
                || body[block].is_cleanup
            {
                continue;
            }

            // is this a loop invariant?
            // (this only considers loop invariants of the current loop)
            if let Some(spec_block) = spec_blocks
                .iter()
                .find(|spec_block| spec_block.attached_to == block)
            {
                invariants_reached.push(spec_block);
                continue;
            }

            match body[block].terminator().kind {
                // keep walking
                mir::TerminatorKind::Goto { target }
                | mir::TerminatorKind::Drop { target, .. }
                | mir::TerminatorKind::Call {
                    target: Some(target),
                    ..
                }
                | mir::TerminatorKind::Assert { target, .. }
                | mir::TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | mir::TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => {
                    queue.push_back(target);
                }
                mir::TerminatorKind::SwitchInt { ref targets, .. } => {
                    queue.extend(targets.all_targets());
                }

                // stop walking
                _ => (),
            }
        }

        // We should have reached exactly one body invariant block. If not,
        // report an error.
        match invariants_reached.len() {
            0 => return Err(PrustiError::incorrect(
                "a `body_invariant!` annotation must be reached unconditionally in every loop iteration".to_string(),
                spec_blocks.iter().map(|b| b.span).collect::<Vec<_>>().into(),
            )),
            1 => (),
            _ => return Err(PrustiError::incorrect(
                "the same `body_invariant!` annotation must be reached unconditionally in every loop iteration".to_string(),
                invariants_reached.iter().map(|b| b.span).collect::<Vec<_>>().into(),
            )),
        }
        assert_eq!(invariants_reached.len(), 1);

        // Finally, we walk the CFG one more time from the one invariant block
        // we reached, this time to find additional consecutive body invariants,
        // not separated by unrelated (non-spec) statements or other blocks.
        let first_invariant = *invariants_reached.first().unwrap();
        let mut queue = VecDeque::new();
        queue.push_back(first_invariant.attached_to);
        let mut consecutive_invariants = Vec::new();

        while let Some(block) = queue.pop_front() {
            // check statements for non-spec local usage
            let block_data = &body[block];
            let mut non_spec_statements = false;
            for stmt in &block_data.statements {
                match stmt.kind {
                    mir::StatementKind::Assign(box (dest, _))
                        if dest.as_local().is_some_and(|local| {
                            !base.spec_arms.spec_only_locals.contains(&local)
                        }) =>
                    {
                        non_spec_statements = true;
                        break;
                    }
                    _ => (),
                }
            }

            // the first invariant block may have non-spec statements (the
            // invariant is only enforced at the terminator)
            if non_spec_statements && block != first_invariant.attached_to {
                continue;
            }

            if let Some(spec_block) = spec_blocks
                .iter()
                .find(|spec_block| spec_block.attached_to == block)
            {
                consecutive_invariants.push(spec_block);
                // add live target to queue
                queue.push_back(base.spec_arms.switches[&spec_block.attached_to]);
                continue;
            }

            // only walk down goto terminators (if we ever find spurious body
            // invariant interruptions, it may be because other terminators
            // appear here)
            if let mir::TerminatorKind::Goto { target } = block_data.terminator().kind {
                queue.push_back(target);
            }
        }

        // Any invariants we did not pick up are placed wrong, report error.
        let unreachable_invariants = spec_blocks
            .iter()
            .filter(|spec_block| !consecutive_invariants.contains(spec_block))
            .collect::<Vec<_>>();
        if !unreachable_invariants.is_empty() {
            return Err(PrustiError::incorrect(
                "`body_invariant!` annotation may not be reached in every loop iteration"
                    .to_string(),
                unreachable_invariants
                    .iter()
                    .map(|spec_block| spec_block.span)
                    .collect::<Vec<_>>()
                    .into(),
            ));
        }

        // Otherwise, the body invariants for this loop are correct.
        Ok(LoopSpec {
            loop_id,
            // The loop head (for our encoding and for querying the PCG) of the
            // loop is the live target of the switch preceding the body
            // invariant. It is not the invariant block itself since that block
            // is spec-only and guarded in `if false`. It is also not the block
            // that the invariant is attached to, because we need the invariant
            // to be attached at the label, and the `attached_to` block may
            // contain statements which mutate the state.
            head_block: base.spec_arms.switches[&first_invariant.attached_to],
            original_head_block,
            invariants: consecutive_invariants
                .into_iter()
                .map(|spec_block| (spec_block.block, spec_block.span))
                .collect(),
        })
    }
}

struct SpecVisitor<'enc, 'vir: 'enc> {
    def_id: DefId,
    body: &'enc mir::Body<'vir>,
    specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    spec_blocks: FxHashSet<BasicBlock>,
    erased_blocks: Vec<BasicBlock>,
    closure_marker_blocks: Vec<BasicBlock>,
    phantom_operands: Vec<mir::Local>,
}

impl<'enc, 'vir: 'enc> SpecVisitor<'enc, 'vir> {
    fn run(def_id: DefId, body: &'enc mir::Body<'vir>) -> Self {
        use mir::visit::Visitor;
        let mut visitor = Self {
            def_id,
            body,
            specs_for: Default::default(),
            spec_blocks: Default::default(),
            erased_blocks: Default::default(),
            closure_marker_blocks: Default::default(),
            phantom_operands: Default::default(),
        };
        visitor.visit_body(body);
        visitor
    }
}

impl<'enc, 'vir: 'enc> mir::visit::Visitor<'vir> for SpecVisitor<'enc, 'vir> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        vir::with_vcx(|vcx| {
            let env_query = EnvQuery::new(vcx.tcx());
            let mir::TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                return;
            };
            let func_ty = func.ty(self.body, vcx.tcx());
            let (def_id, arg_tys) = RustSignature::get_def_id_and_caller_substs(func_ty);
            if !env_query.is_function_in_crate(self.def_id, def_id, arg_tys, "prusti_contracts") {
                return;
            }

            let item_name = vcx.tcx().item_name(def_id);
            match item_name.as_str() {
                "spec_block" => (),
                // The runtime stand-in arm of a `ghost!` block; turned into
                // [GhostBlocks] by the callers.
                "ghost_erased" => {
                    self.erased_blocks.push(location.block);
                    return;
                }
                // The `closure!` spec marker arms are invisible in the
                // encoding: the spec closures they reference are encoded
                // separately as the closure's contract. Turned into
                // [SpecArms] by the callers.
                "closure_spec_pre" => {
                    self.closure_marker_blocks.push(location.block);
                    return;
                }
                // The second argument of args/post is the `PhantomData`
                // binding tying the marker types together, moved from a
                // temporary.
                "closure_spec_args" | "closure_spec_post" => {
                    self.closure_marker_blocks.push(location.block);
                    let local = args[1]
                        .node
                        .place()
                        .and_then(|place| place.as_local())
                        .expect("closure spec marker: `PhantomData` argument is not a local");
                    debug_assert!(
                        self.body.local_decls[local]
                            .ty
                            .ty_adt_def()
                            .is_some_and(|adt| vcx
                                .tcx()
                                .is_lang_item(adt.did(), hir::LangItem::PhantomData)),
                        "closure spec marker: argument is not a `PhantomData`"
                    );
                    self.phantom_operands.push(local);
                    return;
                }
                _ => return,
            }

            let (cl_def_id, _) =
                RustSignature::get_def_id_and_caller_substs(arg_tys[1].expect_ty());
            let cl_attrs = EnvQuery::new(vcx.tcx()).get_attributes(cl_def_id);

            let kind = if has_prusti_attr(cl_attrs, "loop_body_invariant_spec") {
                SpecBlockKind::LoopInvariant
            } else if has_prusti_attr(cl_attrs, "prusti_assertion") {
                SpecBlockKind::Assert
            } else if has_prusti_attr(cl_attrs, "prusti_assumption") {
                SpecBlockKind::Assume
            } else if has_prusti_attr(cl_attrs, "prusti_refutation") {
                SpecBlockKind::Refute
            } else {
                unreachable!("malformed spec-only block: unknown spec kind");
            };

            let nonspec_predecessor =
                get_single_predecessor(&self.body.basic_blocks.predecessors()[location.block]);
            self.specs_for
                .entry(nonspec_predecessor)
                .or_default()
                .push(SpecBlock {
                    attached_to: nonspec_predecessor,
                    block: location.block,
                    kind,
                    span: terminator.source_info.span,
                });
            self.spec_blocks.insert(location.block);
        });
    }
}

/// Collects the locals used by the *encoded* parts of the visited blocks:
/// statements that encode to nothing keep no local alive, and neither do
/// the (skipped) stores to the arms' scaffolding locals (see
/// [SpecArms::scaffolding]).
struct UsedLocals<'enc> {
    arms: &'enc SpecArms,
    unit_candidates: &'enc FxHashSet<mir::Local>,
    used: FxHashSet<mir::Local>,
}

impl<'enc, 'vir> mir::visit::Visitor<'vir> for UsedLocals<'enc> {
    fn visit_local(
        &mut self,
        local: mir::Local,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) {
        self.used.insert(local);
    }

    fn visit_statement(&mut self, statement: &mir::Statement<'vir>, location: mir::Location) {
        match &statement.kind {
            // Not encoded (no-ops in the impure encoder).
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::PlaceMention(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::Coverage(..)
            | mir::StatementKind::ConstEvalCounter
            | mir::StatementKind::Nop
            | mir::StatementKind::BackwardIncompatibleDropHint { .. } => {}
            // Not encoded (stores to scaffolding locals and candidates).
            mir::StatementKind::Assign(box (dest, _))
                if dest.as_local().is_some_and(|local| {
                    self.arms.scaffolding.contains(&local) || self.unit_candidates.contains(&local)
                }) => {}
            _ => self.super_statement(statement, location),
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        // A guarding switch is encoded as a bare goto: its discriminant
        // operand is not used.
        if !self.arms.switches.contains_key(&location.block) {
            self.super_terminator(terminator, location);
        }
    }
}

fn get_single_predecessor(predecessors: &[BasicBlock]) -> BasicBlock {
    assert_eq!(
        predecessors.len(),
        1,
        "malformed spec-only block: expected a single predecessor"
    );
    predecessors[0]
}
