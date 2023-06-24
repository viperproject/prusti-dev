use crate::mir_helper::*;
use prusti_interface::{
    environment::{blocks_dominated_by, is_check_closure, is_marked_check_block, EnvQuery},
    utils::has_prusti_attr,
};
use prusti_rustc_interface::{
    ast::ast,
    middle::{
        mir::{self, visit::Visitor, Statement, StatementKind},
        ty::TyCtxt,
    },
    span::Span,
};
use rustc_hash::{FxHashMap, FxHashSet};

pub struct MirInfo {
    pub moved_args: FxHashMap<mir::Local, mir::Local>,
    pub check_blocks: FxHashMap<mir::BasicBlock, CheckBlockKind>,
}

pub fn collect_mir_info<'tcx>(tcx: TyCtxt<'tcx>, body: mir::Body<'tcx>) -> MirInfo {
    let check_blocks = collect_check_blocks(tcx, &body);
    let mut visitor = MirInfoCollector::new(body.clone());
    visitor.visit_body(&body);
    println!("CHECK BLOCKS: {:#?}", &check_blocks);
    // TODO: update after changes to resolving of old:
    MirInfo {
        moved_args: Default::default(),
        check_blocks,
    }
}

// A MIR Visitor that collects information before we actually start modifying
// the MIR. It's responsibilities are:
// - finding variables that are just copies / moves of arguments
// - finding basic-blocks, that can contain old expressions that should be
//   resolved (check_only blocks)
// - finding basic blocks, that contain an empty closure, referring to an
//   expiration location (when a user manually inserts `prusti_pledge_expires!()`)
//   or blocks that are dominated by this kind of block
struct MirInfoCollector<'tcx> {
    /// locals that are passed to old as arguments
    old_args: FxHashSet<mir::Local>,
    /// dependencies between locals.
    locals_dependencies: FxHashMap<mir::Local, Vec<Dependency>>,
    /// locations where we assign values to locals:
    assignment_locations: FxHashMap<mir::Local, Vec<mir::Location>>,
    /// a body of the copy
    body: mir::Body<'tcx>,
}

#[derive(Clone, Debug)]
struct Dependency {
    local: mir::Local,
    is_user_declared: bool,
    declared_within_old: bool,
    is_mutable_arg: bool,
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

impl<'tcx> Visitor<'tcx> for MirInfoCollector<'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: mir::Location) {
        self.super_statement(statement, location);
        match &statement.kind {
            StatementKind::Assign(box (recv, rvalue)) => {
            }
            _ => (),
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: mir::Location) {
        self.super_terminator(terminator, location);
    }
}

impl<'tcx> MirInfoCollector<'tcx> {
    pub(crate) fn new(body: mir::Body<'tcx>) -> Self {
        Self {
            old_args: Default::default(),
            locals_dependencies: Default::default(),
            assignment_locations: Default::default(),
            body,
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
        println!("Looking for dominated blocks of {:?}", bb);
        let dominated_blocks = blocks_dominated_by(body, bb);
        for bb_dominated in dominated_blocks {
            if bb_dominated != bb {
                println!("\tblock {:?}", bb_dominated);
                assert!(check_blocks.get(&bb_dominated).is_none());
                check_blocks.insert(bb_dominated, bb_kind);
            }
        }
    }
    check_blocks
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
    pub fn determine_kind<'tcx>(
        env_query: EnvQuery<'tcx>,
        bb_data: &mir::BasicBlockData,
    ) -> Option<Self> {
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

// Given a local variable, find all statements or terminators that assign to it.
pub fn find_local_dependencies<'tcx>(
    local: mir::Local,
    body: &mir::Body<'tcx>,
) -> Vec<mir::Location> {
    let mut locations = Vec::new();
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        // check terminator:
        if let mir::TerminatorKind::Call { destination, .. } = bb_data.terminator().kind {
            if destination.local == local {
                locations.push(mir::Location {
                    block: bb,
                    statement_index: bb_data.statements.len(),
                })
            }
        }
        for (index, stmt) in bb_data.statements.iter().enumerate() {
            if let mir::StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.local == local {
                    locations.push(mir::Location {
                        block: bb,
                        statement_index: index,
                    });
                }
            }
        }
    }
    locations
}

struct RvalueVisitor {
    pub dependencies: Vec<mir::Local>,
}

impl<'tcx> Visitor<'tcx> for RvalueVisitor {
    fn visit_local(
        &mut self,
        local: mir::Local,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        self.dependencies.push(local);
    }
}

// find locals that are used to compute the rhs of an assignment
// pub fn find_stmt_dependencies<'tcx>(stmt: Either<&mir::Statement<'tcx>, &mir::Terminator<'tcx>>, location: mir::Location) -> Vec<mir::Local> {
//     let mut visitor = RvalueVisitor {
//         dependencies: Vec::new(),
//     };
//     match stmt {
//         Either::Left(stmt) => {
//             if let mir::StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
//                 visitor.visit_rvalue(rvalue, location);
//             }
//         },
//         Either::Right(term) => {
//             if let mir::TerminatorKind::Call { args, .. } = &term.kind {
//                 for arg in args {
//                     visitor.visit_operand(arg, location);
//                 }
//             }
//         }
//     }
//     visitor.dependencies
// }

// Given the span of the old call, figure if a local is user declared, and also
// whether it was declared outside of the old call.
// Example: we want to differentiate old({let a = b, old(a)}) from
// {let a = b; old(a)}, since, if b is an argument, for the first one we actually
// want the old state of a (on function entry), but not for the second one.
pub fn local_user_declared_outside_old<'tcx>(
    old_span: Span,
    body: &mir::Body<'tcx>,
    local: mir::Local,
) -> bool {
    let local_decl = body.local_decls.get(local).unwrap();
    if local_decl.is_user_variable() {
        old_span.contains(local_decl.source_info.span)
    } else {
        false
    }
}

// pub fn find_arg_dependencies<'tcx>(local: mir::Local, body: &mir::Body<'tcx>) -> Vec<(mir::Local, mir::Local)> {
//     // find locations where we assign to this local
//     let def_locations = find_assignments(local, body);
//     for loc in def_locations{
//         let stmt = body.stmt_at(loc);
//         find_stmt_dependencies(stmt, loc);
//     }
// }
