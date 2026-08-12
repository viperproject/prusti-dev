use pcg::r#loop::{LoopAnalysis, LoopId};
use prusti_interface::{environment::EnvQuery, utils::has_prusti_attr};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::{self, BasicBlock},
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::mir_fn::RustSignature;

#[derive(Clone, Debug)]
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
/// and friends, and the runtime `ghost_erased()` stand-in arms of `ghost!`.
/// The arms are invisible in the encoding: each guarding switch is encoded
/// as an unconditional jump to the live target (the continuation, or the
/// inline ghost body), the arm's blocks are never encoded, and neither are
/// the [spec-only locals](Self::spec_only_locals) nor the (constant)
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
    /// [scaffolding](Self::scaffolding), whose stores are skipped. Neither
    /// their declarations (and hence types) nor the assignments to them are
    /// encoded.
    pub spec_only_locals: FxHashSet<mir::Local>,
    /// The arms' scaffolding locals, each identified by its structural
    /// anchor: the switch discriminants (the operands of the switches
    /// encoded as gotos; their `const false` stores are their only encodable
    /// mention) and the unit values of the arms' `if` statements (stored
    /// `const ()` in the live continuations, kept only when nothing else
    /// uses them: a live unit local in the same block is not scaffolding).
    /// Stores to these locals are not encoded.
    scaffolding: FxHashSet<mir::Local>,
}

impl SpecArms {
    fn new(
        body: &mir::Body<'_>,
        ghost: &GhostBlocks,
        marker_blocks: impl IntoIterator<Item = BasicBlock>,
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

        // The locals assigned within the arms. A `ghost_erased` stand-in arm
        // writes the same destination as its (encoded) ghost arm, and the
        // return place is of course live.
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

    /// Records the spec-only arm containing the given `spec_block` call.
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
    has_body_invariant: bool,
    pub loop_id: LoopId,

    /// Loop head as identified by the PCG.
    #[allow(dead_code)]
    pub original_head_block: BasicBlock,

    /// Loop head as identified by Prusti, i.e., the body invariant, or the
    /// original loop head if no body invariant is present.
    pub head_block: BasicBlock,

    pub invariants: Vec<(BasicBlock, Span)>,
}

#[derive(Clone, Debug)]
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
        let spec_arms = SpecArms::new(body, &ghost, visitor.spec_blocks.iter().copied());

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
        // Associate specs and determine loop heads (at body invariants) for loops
        let mut loop_specs: FxHashMap<LoopId, LoopSpec> = Default::default();

        // For any loop that is not specified with a body invariant (determined
        // above), we default to the loop head being at the loop head identified
        // by the PCG, with no specs.
        for (block, _) in body.basic_blocks.iter_enumerated() {
            let Some(loop_id) = loop_analysis.loop_head_of(block) else {
                continue;
            };

            loop_specs.insert(
                loop_id,
                LoopSpec {
                    has_body_invariant: false,
                    loop_id,
                    head_block: block,
                    original_head_block: block,
                    invariants: Vec::new(),
                },
            );
        }

        for specified_blocks in base.specs_for.values() {
            for spec_block in specified_blocks {
                let SpecBlockKind::LoopInvariant = spec_block.kind else {
                    continue;
                };
                let loop_id = loop_analysis
                    .innermost_loop(spec_block.block)
                    .expect("malformed spec-only block: body invariant not in a loop");
                let loop_spec = loop_specs.get_mut(&loop_id).unwrap();
                if loop_spec.has_body_invariant {
                    panic!(
                        "multiple body invariant annotations are not supported yet (at {:?})",
                        spec_block.span
                    );
                }
                loop_spec.has_body_invariant = true;
                // TODO: is the iteration order of blocks well defined here?
                //   do we always consider the first or last body invariant's
                //   predecessor to be the loop head?
                // The loop head (for our encoding and for querying the PCG) of
                // the loop is the non-spec block preceding the body invariant.
                // It's not the invariant block itself since that block is
                // spec-only and guarded in `if false`.
                loop_spec.head_block = spec_block.attached_to;
                loop_spec
                    .invariants
                    .push((spec_block.block, spec_block.span));
            }
        }

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
}

struct SpecVisitor<'enc, 'vir: 'enc> {
    def_id: DefId,
    body: &'enc mir::Body<'vir>,
    specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    spec_blocks: FxHashSet<BasicBlock>,
    erased_blocks: Vec<BasicBlock>,
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
        };
        visitor.visit_body(body);
        visitor
    }
}

impl<'enc, 'vir: 'enc> mir::visit::Visitor<'vir> for SpecVisitor<'enc, 'vir> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        vir::with_vcx(|vcx| {
            let env_query = EnvQuery::new(vcx.tcx());
            let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
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
