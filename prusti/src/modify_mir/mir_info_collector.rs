use super::mir_helper::*;

use prusti_interface::{
    environment::{blocks_dominated_by, is_check_closure, EnvQuery, Environment},
    globals,
    specs::typed::DefSpecificationMap,
};
use prusti_rustc_interface::{
    middle::{
        mir::{self, visit::Visitor},
        ty::TyCtxt,
    },
    span::{def_id::DefId, Span},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::hash::Hash;

// Info about a specific MIR Body that can be collected before we
// actuallye start modifying it.
// Note that depending on the modifications we perform, some of the
// information (e.g. about blocks might no longer be accurate)
pub struct MirInfo<'tcx> {
    pub def_id: DefId,
    pub specs: DefSpecificationMap,
    pub env: Environment<'tcx>,
    /// function arguments that have to be cloned on entry of the function
    pub args_to_be_cloned: FxHashSet<mir::Local>,
    /// statements in which we should replace the occurrence of a function
    /// argument with their clone
    pub stmts_to_substitute_rhs: FxHashSet<mir::Location>,
    /// the basic blocks that are marked with #[check_only] or dominated by a
    /// block that is
    pub check_blocks: FxHashSet<mir::BasicBlock>,
}

impl<'tcx> MirInfo<'tcx> {
    /// Given a body, collect information about it.
    pub fn collect_mir_info(
        tcx: TyCtxt<'tcx>,
        body: mir::Body<'tcx>,
        def_id: DefId,
    ) -> MirInfo<'tcx> {
        let specs = globals::get_defspec();
        let env = globals::get_env();
        let check_blocks = collect_check_blocks(tcx, &body);
        let (args_to_be_cloned, stmts_to_substitute_rhs) =
            determine_modifications_old_resolution(tcx, body, &check_blocks);
        MirInfo {
            def_id,
            specs,
            env,
            args_to_be_cloned,
            stmts_to_substitute_rhs,
            check_blocks,
        }
    }
    // when MirInfo is no longer required, put specs and env back into global statics
    // (because we only want to / can compute them once)
    pub fn store_specs_env(self) {
        let MirInfo { specs, env, .. } = self;
        globals::store_spec_env(specs, env);
    }
}

/// Figures out which arguments need to be cloned, and in which locations
/// arguments need to be replaced with their clones
fn determine_modifications_old_resolution<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: mir::Body<'tcx>,
    check_blocks: &FxHashSet<mir::BasicBlock>,
) -> (FxHashSet<mir::Local>, FxHashSet<mir::Location>) {
    // find_old_spans..
    let (old_spans, old_args) = find_old_spans_and_args(tcx, &body, check_blocks);

    let mut args_to_clone = FxHashSet::<mir::Local>::default();
    let mut stmts_to_adjust = FxHashSet::<mir::Location>::default();
    let mut encountered = FxHashSet::<mir::Local>::default();

    let mut visitor = DependencyCollector {
        old_spans,
        locals_dependencies: Default::default(),
        assignment_locations: Default::default(),
        body: body.clone(),
    };
    visitor.visit_body(&body);

    for old_arg in old_args.iter() {
        // For each old argument, try to figure out on which function arguments
        // it depends on, and in which locations of the MIR these function arguments
        // need to be replaced with their old values
        let mut to_process = vec![*old_arg];
        while let Some(local) = to_process.pop() {
            let deps = visitor.locals_dependencies.get(&local).unwrap();
            // all the locations this variable has been assigned to
            let assignment_locations = visitor
                .assignment_locations
                .get(&local)
                .cloned()
                .unwrap_or_default();
            deps.iter().for_each(|dep| {
                if dep.is_mutable_arg {
                    // the case where we find a dependency on a function argument, meaning
                    // at this location the function argument will have to be replaced with
                    // an old clone
                    // 1. mark this function argument to be cloned
                    args_to_clone.insert(dep.local);
                    // 2. In the locations where this local is assigned to, we will have to
                    // replace occurrences of this function argument on the rhs with the old clone
                    assignment_locations.iter().for_each(|location| {
                        stmts_to_adjust.insert(*location);
                    });
                } else if (!dep.is_user_declared || dep.declared_within_old)
                    && !encountered.contains(&dep.local)
                {
                    // process this variable too!
                    to_process.push(dep.local);
                    encountered.insert(dep.local);
                }
            });
        }
    }
    (args_to_clone, stmts_to_adjust)
}

// A MIR Visitor that collects information before we actually start modifying
// the MIR. It's responsibilities are:
// - finding function arguments that need to be cloned
// - finding basic-blocks, that can contain old expressions that should be
//   resolved (check_only blocks)
struct DependencyCollector<'tcx> {
    old_spans: Vec<Span>,
    /// dependencies between locals, for each local get a list of other locals
    /// that it depends on
    locals_dependencies: FxHashMap<mir::Local, FxHashSet<Dependency>>,
    /// locations where we assign values to locals:
    assignment_locations: FxHashMap<mir::Local, FxHashSet<mir::Location>>,
    /// a body of the copy
    body: mir::Body<'tcx>,
}

#[derive(Hash, Clone, Debug, PartialEq, Eq)]
struct Dependency {
    local: mir::Local,
    is_user_declared: bool,
    declared_within_old: bool,
    is_mutable_arg: bool,
}

impl<'tcx> DependencyCollector<'tcx> {
    // determine all the relevant facts about this local
    fn create_dependency(&self, local: mir::Local) -> Dependency {
        let local_decl = self.body.local_decls.get(local);

        // calling is_user_variable directly leads to panics for certain variables..
        let is_user_declared = if let Some(local_decl) = local_decl {
            matches!(local_decl.local_info.as_ref(), mir::ClearCrossCrate::Set(_))
                && local_decl.is_user_variable()
        } else {
            false
        };
        // if a variable is not user declared this doesn't matter
        let declared_within_old = is_user_declared
            && self
                .old_spans
                .iter()
                .any(|old_span| old_span.contains(local_decl.unwrap().source_info.span));
        let is_mutable_arg = is_mutable_arg(&self.body, local, &self.body.local_decls);
        Dependency {
            local,
            is_user_declared,
            declared_within_old,
            is_mutable_arg,
        }
    }
}

impl<'tcx> Visitor<'tcx> for DependencyCollector<'tcx> {
    fn visit_statement(&mut self, statement: &mir::Statement<'tcx>, location: mir::Location) {
        self.super_statement(statement, location);
        if let mir::StatementKind::Assign(box (recv, rvalue)) = &statement.kind {
            // store this location as one where we assign to this local
            self.assignment_locations
                .entry(recv.local)
                .or_default()
                .insert(location);
            // collect all locals contained in rhs rvalue and add them as dependencies
            let dependencies = rvalue_dependencies(rvalue, location);
            dependencies.iter().for_each(|local| {
                let dep = self.create_dependency(*local);
                self.locals_dependencies
                    .entry(recv.local)
                    .or_default()
                    .insert(dep);
            });
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        self.super_terminator(terminator, location);
        // find calls and their dependencies:
        if let mir::TerminatorKind::Call {
            args, destination, ..
        } = &terminator.kind
        {
            // Store this location as one where we assign to this local
            self.assignment_locations
                .entry(destination.local)
                .or_default()
                .insert(location);
            // Add each argument as a dependency for the lefhandside of this call
            args.iter().for_each(|arg| {
                if let mir::Operand::Move(place) | mir::Operand::Copy(place) = arg {
                    let dep = self.create_dependency(place.local);
                    self.locals_dependencies
                        .entry(destination.local)
                        .or_default()
                        .insert(dep);
                }
            });
        }
    }
}

fn rvalue_dependencies(rvalue: &mir::Rvalue<'_>, location: mir::Location) -> Vec<mir::Local> {
    struct RvalueVisitor {
        pub dependencies: Vec<mir::Local>,
    }
    impl<'tcx> Visitor<'tcx> for RvalueVisitor {
        fn visit_local(
            &mut self,
            local: mir::Local,
            _context: mir::visit::PlaceContext,
            _location: mir::Location,
        ) {
            self.dependencies.push(local);
        }
    }
    let mut visitor = RvalueVisitor {
        dependencies: vec![],
    };
    visitor.visit_rvalue(rvalue, location);
    visitor.dependencies
}

fn find_old_spans_and_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    check_blocks: &FxHashSet<mir::BasicBlock>,
) -> (Vec<Span>, FxHashSet<mir::Local>) {
    struct OldSpanFinder<'tcx, 'a> {
        tcx: TyCtxt<'tcx>,
        old_spans: Vec<Span>,
        old_args: FxHashSet<mir::Local>,
        check_blocks: &'a FxHashSet<mir::BasicBlock>,
    }
    // spans of old calls need to be resolved first, so we can determine
    // whether locals are defined inside them later.
    impl<'tcx, 'a> Visitor<'tcx> for OldSpanFinder<'tcx, 'a> {
        fn visit_terminator(
            &mut self,
            terminator: &mir::Terminator<'tcx>,
            location: mir::Location,
        ) {
            self.super_terminator(terminator, location);
            if let mir::TerminatorKind::Call {
                func,
                args,
                fn_span,
                ..
            } = &terminator.kind
            {
                if let Some((call_id, _)) = func.const_fn_def() {
                    let item_name = self.tcx.def_path_str(call_id);
                    if item_name == "prusti_contracts::old"
                        && self.check_blocks.contains(&location.block)
                    {
                        self.old_spans.push(*fn_span);
                        assert!(args.len() == 1);
                        if let mir::Operand::Copy(place) | mir::Operand::Move(place) =
                            args.get(0).unwrap()
                        {
                            self.old_args.insert(place.local);
                        }
                    }
                }
            }
        }
    }
    let mut finder = OldSpanFinder {
        tcx,
        old_spans: Default::default(),
        old_args: Default::default(),
        check_blocks,
    };
    finder.visit_body(body);
    (finder.old_spans, finder.old_args)
}

/// Figure out which of the blocks of this body contain a closure marked with
/// #[check_only] or are dominated by such a block
pub fn collect_check_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> FxHashSet<mir::BasicBlock> {
    let env_query = EnvQuery::new(tcx);
    let mut marked_check_blocks = FxHashSet::default();
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        if is_check_block(env_query, bb_data) {
            marked_check_blocks.insert(bb);
        }
    }
    // all the blocks that are dominated by one of these check blocks, are check
    // blocks of the same kind too. No two blocks should be dominated by
    // more than one block containing such a closure.
    let mut check_blocks = marked_check_blocks.clone();
    for bb in marked_check_blocks {
        let dominated_blocks = blocks_dominated_by(body, bb);
        for bb_dominated in dominated_blocks {
            if bb_dominated != bb {
                check_blocks.insert(bb_dominated);
            }
        }
    }
    check_blocks
}

/// Goes through the statements of a block, and looks for a closure that is
/// annotated with #[check_only], marking the blocks that start a runtime
/// check for things like prusti_assert, prusti_assume, and loop_invariant
fn is_check_block(env_query: EnvQuery<'_>, bb_data: &mir::BasicBlockData) -> bool {
    for stmt in &bb_data.statements {
        if let mir::StatementKind::Assign(box (
            _,
            mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(def_id, _), _),
        )) = stmt.kind
        {
            if is_check_closure(env_query, def_id) {
                return true;
            }
        }
    }
    false
}
