use pcg::r#loop::{LoopAnalysis, LoopId};
use prusti_interface::{environment::EnvQuery, utils::has_prusti_attr};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::{self, BasicBlock},
    span::{Span, def_id::DefId},
};

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
#[derive(Default)]
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
        let mut ghost = GhostBlocks::default();
        vir::with_vcx(|vcx| {
            let env_query = EnvQuery::new(vcx.tcx());
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let mir::TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    continue;
                };
                let func_ty = func.ty(body, vcx.tcx());
                let (fn_def_id, arg_tys) = RustSignature::get_def_id_and_caller_substs(func_ty);
                if env_query.is_function_in_crate(def_id, fn_def_id, arg_tys, "prusti_contracts")
                    && vcx.tcx().item_name(fn_def_id).as_str() == "ghost_erased"
                {
                    ghost.visit_erased(body, block);
                }
            }
        });
        ghost
    }

    /// Records the ghost block whose runtime stand-in arm is `erased_block`.
    fn visit_erased(&mut self, body: &mir::Body<'_>, erased_block: BasicBlock) {
        let switch_block = get_single_predecessor(&body.basic_blocks.predecessors()[erased_block]);
        let mir::TerminatorKind::SwitchInt { targets, .. } = &body[switch_block].terminator().kind
        else {
            unreachable!("malformed ghost block: `ghost_erased` arm not guarded by a switch");
        };
        let mut siblings = targets
            .all_targets()
            .iter()
            .copied()
            .filter(|target| *target != erased_block);
        let arm_block = siblings
            .next()
            .expect("malformed ghost block: no sibling arm");
        assert!(
            siblings.next().is_none(),
            "malformed ghost block: expected a two-armed switch"
        );
        self.switches.insert(
            switch_block,
            GhostBlock {
                arm_block,
                erased_block,
            },
        );

        // The ghost arm's blocks (the inline ghost body): everything
        // reachable from (and still dominated by) the arm entry. The
        // dominance requirement keeps blocks shared with live code out of
        // the region (the join both arms continue to, and cleanup blocks
        // that calls outside the arm also unwind to).
        let doms = body.basic_blocks.dominators();
        let mut queue = vec![arm_block];
        while let Some(block) = queue.pop() {
            if !doms.dominates(arm_block, block) || !self.code.insert(block) {
                continue;
            }
            queue.extend(body.basic_blocks[block].terminator().successors());
        }
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
    /// Set of all spec-only blocks.
    pub spec_blocks: FxHashSet<BasicBlock>,
    /// Set of loop specifications, keyed by loop heads.
    pub loop_specs: FxHashMap<BasicBlock, LoopSpec>,
    /// Maps loop IDs (as identified by the PCG loop analysis) to their loop
    /// heads.
    pub loop_head_at: FxHashMap<LoopId, BasicBlock>,
    /// The `ghost!` blocks of the body.
    pub ghost: GhostBlocks,
}

impl SpecBlocks {
    /// Determine the spec-only blocks for the given MIR body. Spec-only blocks
    /// are ones which consists of *only* a closure assignment of a closure
    /// marked with the Prusti spec-only attribute. For each spec-only block we
    /// determine which non-spec block it is attached to.
    pub fn new<'enc, 'vir: 'enc>(
        def_id: DefId,
        body: &'enc mir::Body<'vir>,
        loop_analysis: &'enc LoopAnalysis,
    ) -> Self {
        use mir::visit::Visitor;
        let mut visitor = SpecVisitor {
            def_id,
            body,
            specs_for: Default::default(),
            spec_blocks: Default::default(),
        };
        visitor.visit_body(body);

        // The runtime stand-in arms of ghost blocks are skipped in the
        // encoding (their switches are encoded as unconditional jumps into
        // the ghost arms).
        let ghost = GhostBlocks::new(def_id, body);
        visitor
            .spec_blocks
            .extend(ghost.switches.values().map(|g| g.erased_block));

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

        for specified_blocks in visitor.specs_for.values() {
            for spec_block in specified_blocks {
                // If this assertion ever fails, then consecutive spec blocks
                // are actually consecutive blocks in the CFG. If this happens,
                // we need to keep walking up the predecessors for each spec
                // block until we find a non-spec block.
                assert!(!visitor.spec_blocks.contains(&spec_block.attached_to));

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
            specs_for: visitor.specs_for,
            spec_blocks: visitor.spec_blocks,
            loop_specs,
            loop_head_at,
            ghost,
        }
    }
}

struct SpecVisitor<'enc, 'vir: 'enc> {
    def_id: DefId,
    body: &'enc mir::Body<'vir>,
    specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    spec_blocks: FxHashSet<BasicBlock>,
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
            if item_name.as_str() != "spec_block" {
                return;
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

fn get_single_predecessor(predecessors: &[BasicBlock]) -> BasicBlock {
    assert_eq!(
        predecessors.len(),
        1,
        "malformed spec-only block: expected a single predecessor"
    );
    predecessors[0]
}
