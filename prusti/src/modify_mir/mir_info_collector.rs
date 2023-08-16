use super::mir_helper::*;

use prusti_interface::{
    environment::{blocks_dominated_by, is_check_closure, EnvQuery, Environment},
    globals,
    specs::typed::DefSpecificationMap,
    utils::has_prusti_attr,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, visit::Visitor, Statement, StatementKind},
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
    /// blocks that the translation specifically added to either mark
    /// a location (manual pledge expiry) or that we identified to
    /// be the check blocks for a `prusti_assert!`, `prusti_assume!` or
    /// `body_invariant`.
    pub check_blocks: FxHashMap<mir::BasicBlock, CheckBlockKind>,
    /// function arguments that have to be cloned on entry of the function
    pub args_to_be_cloned: FxHashSet<mir::Local>,
    /// statements in which we should replace the occurrence of a function
    /// argument with their clone
    pub stmts_to_substitute_rhs: FxHashSet<mir::Location>,
}

impl<'tcx> MirInfo<'tcx> {
    // Collect this info given a body.
    // mir_promoted is also passed in here, because some information
    // is removed in mir_drops_elaborated
    pub fn collect_mir_info<'a>(
        tcx: TyCtxt<'tcx>,
        body: mir::Body<'tcx>,
        def_id: DefId,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    ) -> MirInfo<'tcx> {
        let specs = globals::get_defspec();
        let env = globals::get_env();
        let check_blocks = collect_check_blocks(tcx, &body);
        let mut visitor = MirInfoCollector::new(body.clone(), tcx, local_decls);
        visitor.visit_body(&body);
        let (args_to_be_cloned, stmts_to_substitute_rhs) = visitor.process_dependencies();
        MirInfo {
            def_id,
            specs,
            env,
            check_blocks,
            args_to_be_cloned,
            stmts_to_substitute_rhs,
        }
    }
    // when MirInfo is no longer required, put specs and env back into
    // global statics (because we only want to compute them once)
    // consider putting this inside of drop for MirInfo
    pub fn store_specs_env(self) {
        let MirInfo { specs, env, .. } = self;
        globals::store_spec_env(specs, env);
    }
}

// A MIR Visitor that collects information before we actually start modifying
// the MIR. It's responsibilities are:
// - finding function arguments that need to be cloned
// - finding basic-blocks, that can contain old expressions that should be
//   resolved (check_only blocks)
// - finding basic blocks, that contain an empty closure, referring to an
//   expiration location (when a user manually inserts `prusti_pledge_expires!()`)
//   or blocks that are dominated by this kind of block
struct MirInfoCollector<'tcx, 'a> {
    /// a MIR visitor collecting some information about old calls, run
    /// beforehand
    old_visitor: OldSpanFinder<'tcx>,
    /// dependencies between locals, for each local get a list of other locals
    /// that it depends on
    locals_dependencies: FxHashMap<mir::Local, FxHashSet<Dependency>>,
    /// locations where we assign values to locals:
    assignment_locations: FxHashMap<mir::Local, Vec<mir::Location>>,
    /// a body of the copy
    body: mir::Body<'tcx>,
    /// the rvalue visitor, so we don't construct it for each assignment
    rvalue_visitor: RvalueVisitor,
    local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
}

#[derive(Hash, Clone, Debug, PartialEq, Eq)]
struct Dependency {
    local: mir::Local,
    is_user_declared: bool,
    declared_within_old: bool,
    is_mutable_arg: bool,
}

impl<'tcx, 'a> Visitor<'tcx> for MirInfoCollector<'tcx, 'a> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: mir::Location) {
        self.super_statement(statement, location);
        if let StatementKind::Assign(box (recv, rvalue)) = &statement.kind {
            // collect all locals contained in rvalue.
            self.rvalue_visitor.visit_rvalue(rvalue, location);
            // take the collected locals and reset visitor
            let dependencies = std::mem::take(&mut self.rvalue_visitor.dependencies);
            dependencies.iter().for_each(|local| {
                let dep = self.create_dependency(*local);
                if let Some(dependencies) = self.locals_dependencies.get_mut(&recv.local) {
                    dependencies.insert(dep);
                } else {
                    let dependencies = [dep].iter().cloned().collect();
                    self.locals_dependencies.insert(recv.local, dependencies);
                }
                if let Some(location_vec) = self.assignment_locations.get_mut(&recv.local) {
                    location_vec.push(location);
                } else {
                    self.assignment_locations.insert(recv.local, vec![location]);
                }
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
            // collect dependencies
            args.iter().for_each(|arg| {
                if let mir::Operand::Move(place) | mir::Operand::Copy(place) = arg {
                    let dep = self.create_dependency(place.local);
                    if let Some(dependencies) = self.locals_dependencies.get_mut(&destination.local)
                    {
                        dependencies.insert(dep);
                    } else {
                        let mut dependencies = FxHashSet::default();
                        dependencies.insert(dep);
                        self.locals_dependencies
                            .insert(destination.local, dependencies);
                    };
                    if let Some(location_vec) =
                        self.assignment_locations.get_mut(&destination.local)
                    {
                        location_vec.push(location);
                    } else {
                        let location_vec = vec![location];
                        self.assignment_locations
                            .insert(destination.local, location_vec);
                    };
                }
            });
        }
    }
}

impl<'tcx, 'a> MirInfoCollector<'tcx, 'a> {
    pub(crate) fn new(
        body: mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    ) -> Self {
        // old visitor identifies spans of old within code
        let mut old_visitor = OldSpanFinder::new(tcx);
        old_visitor.visit_body(&body);
        Self {
            old_visitor,
            locals_dependencies: Default::default(),
            assignment_locations: Default::default(),
            body,
            rvalue_visitor: RvalueVisitor {
                dependencies: Default::default(),
            },
            local_decls,
        }
    }

    // Given the dependencies, figure out which arguments we need to clone
    // and which statements will need to be adjusted
    pub fn process_dependencies(&self) -> (FxHashSet<mir::Local>, FxHashSet<mir::Location>) {
        let mut args_to_clone = FxHashSet::<mir::Local>::default();
        let mut stmts_to_adjust = FxHashSet::<mir::Location>::default();
        let mut encountered = FxHashSet::<mir::Local>::default();
        // travers the dependency graph starting at old arguments, stopping
        // at user defined variables defined outside of old, looking for
        // dependencies on mutable function arguments
        for old_arg in self.old_visitor.old_args.iter() {
            // we put locals in here that are dependencies of old arguments and
            // that are not user defined
            let mut to_process = vec![*old_arg];
            while let Some(local) = to_process.pop() {
                let deps = self.locals_dependencies.get(&local).unwrap();
                let assignment_locations = self.assignment_locations.get(&local).unwrap();
                let mut depends_on_argument = false;
                deps.iter().for_each(|dep| {
                    if dep.is_mutable_arg {
                        args_to_clone.insert(dep.local);
                        depends_on_argument = true;
                    } else if (!dep.is_user_declared || dep.declared_within_old)
                        && !encountered.contains(&dep.local)
                    {
                        // process this variable too!
                        to_process.push(dep.local);
                        encountered.insert(dep.local);
                    }
                });
                if depends_on_argument {
                    // we potentially have to replace function arguments with cloned
                    // values in the places these locals are assigned to
                    assignment_locations.iter().for_each(|location| {
                        stmts_to_adjust.insert(*location);
                    });
                }
            }
        }
        (args_to_clone, stmts_to_adjust)
    }
    // determine all the relevant facts about this local
    fn create_dependency(&self, local: mir::Local) -> Dependency {
        let local_decl = self.local_decls.get(local);

        // is_user_variable leads to panics for certain variables..
        let is_user_declared = if let Some(local_decl) = local_decl {
            matches!(local_decl.local_info.as_ref(), mir::ClearCrossCrate::Set(_))
                && local_decl.is_user_variable()
        } else {
            false
        };
        // if a variable is not user declared this doesn't matter
        let declared_within_old = is_user_declared
            && self
                .old_visitor
                .old_spans
                .iter()
                .any(|old_span| old_span.contains(local_decl.unwrap().source_info.span));
        let is_mutable_arg = is_mutable_arg(&self.body, local, self.local_decls);
        Dependency {
            local,
            is_user_declared,
            declared_within_old,
            is_mutable_arg,
        }
    }
}

pub fn collect_check_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> FxHashMap<mir::BasicBlock, CheckBlockKind> {
    let env_query = EnvQuery::new(tcx);
    let mut marked_check_blocks = FxHashMap::default();
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        if let Some(kind) = CheckBlockKind::determine_kind(env_query, bb_data) {
            marked_check_blocks.insert(bb, kind);
        }
    }
    // all the blocks that are dominated by one of these check blocks, are check
    // blocks of the same kind too. No two blocks should be dominated by
    // more than one block containing such a closure.
    let mut check_blocks = marked_check_blocks.clone();
    for (bb, bb_kind) in marked_check_blocks {
        let dominated_blocks = blocks_dominated_by(body, bb);
        for bb_dominated in dominated_blocks {
            if bb_dominated != bb {
                assert!(check_blocks.get(&bb_dominated).is_none());
                check_blocks.insert(bb_dominated, bb_kind);
            }
        }
    }
    check_blocks
}

/// This function has the specific purpose of finding the local variable that
/// contains the result of a pledge when processing a pledge_expires annotation.
/// it's always assigned to a local variable directly after the empty closure
fn first_variable_assignment(bb_data: &mir::BasicBlockData) -> Option<mir::Local> {
    for stmt in &bb_data.statements {
        if let mir::StatementKind::Assign(box (_, mir::Rvalue::Use(mir::Operand::Move(place)))) =
            stmt.kind
        {
            return Some(place.local);
        }
    }
    None
}

#[derive(Clone, Copy, Debug)]
pub enum CheckBlockKind {
    /// comes from either assume, assert or bodyinvariant
    RuntimeAssertion,
    /// a manually annotated location by the user, where a pledge expires
    /// containing the local that stores this pledge
    PledgeExpires(mir::Local),
}

impl CheckBlockKind {
    pub fn determine_kind(env_query: EnvQuery<'_>, bb_data: &mir::BasicBlockData) -> Option<Self> {
        for stmt in &bb_data.statements {
            if let mir::StatementKind::Assign(box (
                _,
                mir::Rvalue::Aggregate(box mir::AggregateKind::Closure(def_id, _), _),
            )) = stmt.kind
            {
                if is_check_closure(env_query, def_id) {
                    let attrs = env_query.get_attributes(def_id);
                    if has_prusti_attr(attrs, "expiration_location") {
                        // there needs to be a single assignment
                        let pledge_target = first_variable_assignment(bb_data).unwrap();
                        return Some(Self::PledgeExpires(pledge_target));
                    } else if has_prusti_attr(attrs, "runtime_assertion") {
                        return Some(Self::RuntimeAssertion);
                    }
                }
            }
        }
        None
    }
}

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

struct OldSpanFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    old_spans: Vec<Span>,
    old_args: FxHashSet<mir::Local>,
}

// spans of old calls need to be resolved first, so we can determine
// whether locals are defined inside them later.
impl<'tcx> Visitor<'tcx> for OldSpanFinder<'tcx> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
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
                if &item_name[..] == "prusti_contracts::old" {
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

impl<'tcx> OldSpanFinder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        OldSpanFinder {
            old_spans: Default::default(),
            old_args: Default::default(),
            tcx,
        }
    }
}
