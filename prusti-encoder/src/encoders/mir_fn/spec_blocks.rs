use pcg::r#loop::{LoopAnalysis, LoopId};
use prusti_interface::{environment::EnvQuery, utils::{has_prusti_attr,}};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::{self, BasicBlock},
    span::Span,
};

use crate::encoders::mir_fn::RustSignature;

#[derive(Clone, Debug)]
pub enum SpecBlockKind {
    LoopInvariant,
    GhostStart,
    GhostEnd,
    Assert,
    Assume,
    Refute,
}

#[derive(Debug)]
pub struct LoopSpec {
    has_body_invariant: bool,
    pub loop_id: LoopId,
    pub original_head_block: BasicBlock,
    pub head_block: BasicBlock,
    pub invariants: Vec<BasicBlock>,
}

#[derive(Clone, Debug)]
pub struct SpecBlock {
    pub attached_to: BasicBlock,
    pub block: BasicBlock,
    pub kind: SpecBlockKind,
    pub span: Span,
}

#[derive(Default)]
pub struct SpecBlocks {
    pub specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    pub spec_blocks: FxHashSet<BasicBlock>,
    pub loop_specs: FxHashMap<BasicBlock, LoopSpec>,
}

impl SpecBlocks {
    /// Determine the spec-only blocks for the given MIR body. Spec-only blocks
    /// are ones which consists of *only* a closure assignment of a closure
    /// marked with the Prusti spec-only attribute. For each spec-only block we
    /// determine which non-spec block it is attached to.
    pub fn new<'enc, 'vir: 'enc>(
        body: &'enc mir::Body<'vir>,
        loop_analysis: &'enc LoopAnalysis,
    ) -> Self {
        use mir::visit::Visitor;
        let mut visitor = SpecVisitor {
            body,
            specs_for: Default::default(),
            spec_blocks: Default::default(),
        };
        visitor.visit_body(body);

        // Associate specs and determine loop heads (at body invariants) for loops
        let mut loop_specs: FxHashMap<LoopId, LoopSpec> = Default::default();

        // For any loop that is not specified with a body invariant (determined
        // above), we default to the loop head being at the loop head identified
        // by the PCG, with no specs.
        for (block, _) in body.basic_blocks.iter_enumerated() {
            let Some(loop_id) = loop_analysis.loop_head_of(block) else { continue; };

            loop_specs.insert(loop_id, LoopSpec {
                has_body_invariant: false,
                loop_id,
                head_block: block,
                original_head_block: block,
                invariants: Vec::new(),
            });
        }

        for (_, specified_blocks) in &visitor.specs_for {
            for spec_block in specified_blocks {
                // If this assertion ever fails, then consecutive spec blocks
                // are actually consecutive blocks in the CFG. If this happens,
                // we need to keep walking up the predecessors for each spec
                // block until we find a non-spec block.
                assert!(!visitor.spec_blocks.contains(&spec_block.attached_to));

                let SpecBlockKind::LoopInvariant = spec_block.kind else {
                    continue;
                };
                let loop_id = loop_analysis.innermost_loop(spec_block.block)
                    .expect("malformed spec-only block: body invariant not in a loop");
                let loop_spec = loop_specs.get_mut(&loop_id).unwrap();
                loop_spec.has_body_invariant = true;
                // TODO: is the iteration order of blocks well defined here?
                //   do we always consider the first or last body invariant's
                //   predecessor to be the loop head?
                // The loop head (for our encoding and for querying the PCG) of
                // the loop is the non-spec block preceding the body invariant.
                // It's not the invariant block itself since that block is
                // spec-only and guarded in `if false`.
                loop_spec.head_block = spec_block.attached_to;
                loop_spec.invariants.push(spec_block.block);
            }
        }

        let loop_specs = loop_specs.into_iter()
            .map(|(_loop_id, spec)| (spec.head_block, spec))
            .collect();
        Self {
            specs_for: visitor.specs_for,
            spec_blocks: visitor.spec_blocks,
            loop_specs,
        }
    }
}

struct SpecVisitor<'enc, 'vir: 'enc> {
    body: &'enc mir::Body<'vir>,
    specs_for: FxHashMap<BasicBlock, Vec<SpecBlock>>,
    spec_blocks: FxHashSet<BasicBlock>,
}

impl<'enc, 'vir: 'enc> mir::visit::Visitor<'vir> for SpecVisitor<'enc, 'vir> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'vir>, location: mir::Location) {
        let mut spec_kind = None;
        vir::with_vcx(|vcx| {
            let env_query = EnvQuery::new(vcx.tcx());
            match &terminator.kind {
                mir::TerminatorKind::Call { func, .. } => {
                    let func_ty = func.ty(self.body, vcx.tcx());
                    let (def_id, arg_tys) = RustSignature::get_def_id_and_caller_substs(func_ty);
                    if !env_query.is_function_in_crate(def_id, arg_tys, "prusti_contracts") {
                        return;
                    }

                    let item_name = vcx.tcx().item_name(def_id);
                    if item_name.as_str() != "spec_block" {
                        return;
                    }

                    let (cl_def_id, _) = RustSignature::get_def_id_and_caller_substs(arg_tys[1].expect_ty());
                    let cl_attrs = EnvQuery::new(vcx.tcx()).get_attributes(cl_def_id);

                    spec_kind = Some(if has_prusti_attr(cl_attrs, "loop_body_invariant_spec") {
                        SpecBlockKind::LoopInvariant
                    } else if has_prusti_attr(cl_attrs, "ghost_begin") {
                        SpecBlockKind::GhostStart
                    } else if has_prusti_attr(cl_attrs, "ghost_end") {
                        SpecBlockKind::GhostEnd
                    } else if has_prusti_attr(cl_attrs, "prusti_assertion") {
                        SpecBlockKind::Assert
                    } else if has_prusti_attr(cl_attrs, "prusti_assumption") {
                        SpecBlockKind::Assume
                    } else if has_prusti_attr(cl_attrs, "prusti_refutation") {
                        SpecBlockKind::Refute
                    } else {
                        unreachable!("malformed spec-only block: unknown spec kind");
                    });
                }
                _ => (),
            }
        });
        if let Some(kind) = spec_kind {
            let nonspec_predecessor = get_single_predecessor(&self.body.basic_blocks.predecessors()[location.block]);
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
        }
    }
}

fn get_single_predecessor(predecessors: &[BasicBlock]) -> BasicBlock {
    assert_eq!(predecessors.len(), 1, "malformed spec-only block: expected a single predecessor");
    predecessors[0]
}
