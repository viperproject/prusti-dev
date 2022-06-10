#![allow(dead_code)]
use rustc_data_structures::stable_set::FxHashSet;
use rustc_middle::{
    mir::{Local, Place, PlaceElem},
    ty::List,
};

/*

    Operational MIR
        A rewrite of the MIR into a more operational semantics

    The key differences from MIR are this:
        - OpMir expands MIR operations into many small steps whose PCS can be
            represented simply with pre- and post- conditions.
        - OpMir places are like MIR places, but with an additional projections
            for temporary places (which may or may not be used, and are always
            only used within a MIR assignment)
        - OpMir repsects the frame rule.

        The first OpMir encoding does not support verification along unwinding
        paths, and also does not support borrows.

*/

pub struct OpMirBlock<'tcx> {
    pub statements: Vec<OpMirStatement<'tcx>>,
    pub terminator: OpMirTerminator<'tcx>,
}

/* The pre- and post- conditions are set up this way so that
    we can add to them (int the frame rule sense: we add
    to pre- and post- conditions at the same time and require
    there be no seperating connective conflicts).

  An invariant of a well-annotated OpMir program is that
  each pre- and post- condition is a non-conflicting superset
  of the minimal PCS for each statement.

  pre- and post- conditions can only be None during construction.
  A None condition represents "uncomputed", whereas Some({})
  represents "no condition".
*/
pub struct OpMirStatement<'tcx> {
    pre: Option<FxHashSet<PCSPermission<'tcx>>>,
    post: Option<FxHashSet<PCSPermission<'tcx>>>,
    operator: OpMirOperator<'tcx>,
}

pub struct OpMirTerminator<'tcx> {
    kind: OpMirTerminatorKind,
    pre: Option<FxHashSet<PCSPermission<'tcx>>>,
}

pub enum OpMirTerminatorKind {
    Goto,
    // ...
}

impl OpMirTerminatorKind {
    pub fn core_precondition(&self) {
        todo!();
    }
}

pub enum OpMirOperator<'tcx> {
    /* no-op */
    Nop,
    Set(OpMirPlace<'tcx>, OpMirPlace<'tcx>, Mutability),

    /* Permissions-level model of which places rust will deallocate at a location */
    /* Also used to end the lifetimes of temporary variables? */
    Kill(OpMirPlace<'tcx>),

    /* Clone a place into one of it's temporary projections */
    Duplicate(OpMirPlace<'tcx>, OpMirProjection<'tcx>),
    // ...
}

impl<'tcx> OpMirOperator<'tcx> {
    pub fn core_precondition(&self) -> Option<FxHashSet<PCSPermission>> {
        match self {
            OpMirOperator::Set(dest, assignee, m) => Some(FxHashSet::from_iter([
                PCSPermission::Uninit(dest.clone().into()),
                PCSPermission::new_with_read(*m, assignee.clone().into()),
            ])),
            OpMirOperator::Kill(_) => None,
            OpMirOperator::Duplicate(_, _) => todo!(),
            OpMirOperator::Nop => Some(FxHashSet::default()),
        }
    }

    pub fn core_postcondition(&self) -> Option<FxHashSet<PCSPermission>> {
        match self {
            OpMirOperator::Set(dest, assignee, m) => Some(FxHashSet::from_iter([
                PCSPermission::new_with_read(*m, dest.clone().into()),
                PCSPermission::Uninit(assignee.clone().into()),
            ])),
            OpMirOperator::Kill(p) => Some(FxHashSet::from_iter([PCSPermission::Uninit(
                p.clone().into(),
            )])),
            OpMirOperator::Duplicate(p, project) => todo!(),
            OpMirOperator::Nop => Some(FxHashSet::default()),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PCSPermission<'tcx> {
    Shared(OpMirPlace<'tcx>),
    Exclusive(OpMirPlace<'tcx>),
    Uninit(OpMirPlace<'tcx>),
}

impl<'tcx> PCSPermission<'tcx> {
    // New permission with read perms
    pub fn new_with_read(m: Mutability, p: OpMirPlace<'tcx>) -> Self {
        match m {
            Mutability::Mut => PCSPermission::Exclusive(p),
            Mutability::Not => PCSPermission::Shared(p),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Mutability {
    Mut,
    Not,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct OpMirPlace<'tcx> {
    local: Local,
    projection: OpMirProjection<'tcx>,
}

impl<'tcx> From<Place<'tcx>> for OpMirPlace<'tcx> {
    fn from(p: Place<'tcx>) -> Self {
        todo!();
    }
}

impl<'tcx> From<Local> for OpMirPlace<'tcx> {
    fn from(local: Local) -> Self {
        Self {
            local,
            projection: OpMirProjection::Mir(rustc_middle::ty::List::empty()),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum OpMirProjection<'tcx> {
    Mir(&'tcx List<PlaceElem<'tcx>>),
    Temp(usize),
}

pub fn init_analysis() {}

// TODO ITEMS:
//   Prefix invariant in init semantics
//   Operational translation
//   Calling the conditional analysis (refactored for operational MIR)
//   Kill elaboration into MicroMir
