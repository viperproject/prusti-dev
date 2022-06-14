// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use rustc_data_structures::stable_set::FxHashSet;
use rustc_middle::mir::{Local, Location, Place, PlaceElem};

pub struct MicroMirBlock<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub terminator: MicroMirTerminator<'tcx>,
}

pub struct MicroMirTerminator<'tcx> {
    kind: MicroMirTerminatorKind,
    pre: Option<FxHashSet<PCSPermission<'tcx>>>,
}

// TODO: Design problem: Do we want temporary places?
// It is possible to leak permissions under this encoding, if every temporary isn't used up.
// However, this is pretty easy to check. Any statement-level pre/post conditions should have
// no temporaries.

/// Temporary: representation of an anonymous linear (not affine!) resource.

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct TemporaryPlace {
    id: usize,
}

pub enum MicroMirStatement<'tcx> {
    /// No-Op
    Nop,

    /// Set a Place from a temporary
    Set(TemporaryPlace, Place<'tcx>, Mutability),

    /// Move a place into a temporary place
    Move(Place<'tcx>, TemporaryPlace),

    /// Clone a place into a temporary place
    Duplicate(Place<'tcx>, TemporaryPlace, Mutability),

    /// Assume permission for a constant
    Constant(TemporaryPlace, rustc_middle::mir::Constant<'tcx>),

    // /// Permissions-level model of which places rust will deallocate at a location
    // /// TODO: Also used to end the lifetimes of temporary variables?
    // Kill(Place<'tcx>),

    // /// Computes the length of a place into a temporary
    // Len(Place<'tcx>, TemporaryPlace),

    // /// Performs a nullary op, into a temporary
    // NullOp(rustc_middle::mir::NullOp, TemporaryPlace),

    // /// Performs a Unary op onto a temporary
    // UnaryOp(rustc_middle::mir::UnOp, TemporaryPlace, TemporaryPlace),
    /// Performs a Binary op onto a temporary
    /// (bool) flag if this is a checked binary operation
    BinaryOp(
        rustc_middle::mir::BinOp,
        bool,
        TemporaryPlace,
        TemporaryPlace,
        TemporaryPlace,
    ),
}

pub enum MicroMirTerminatorKind {
    // WIP
    Goto,
    // ...
}

impl MicroMirTerminatorKind {
    // WIP
    pub fn core_precondition(&self) {
        todo!();
    }
}

/// MicroMir permission model
/// Let u/e/s mean uninit/exclusive/shared respectively.
///
/// TODO: I'm not convinced we should use this as a standalone language yet,
/// however it at the very least gives us a way to compute pre- and post-
/// conditions for MIR statements.
///
/// { e t, u q }    Set(t, q, Mut)              { e q }
/// { s t, u q }    Set(t, q, Not)              { s q }
/// { e p }         Move(p, t)                  { u p, e t }
/// { e p }         Duplicate(p, t, Mut)        { e p, e t }
/// { s p }         Duplicate(p, t, Not)        { s p, e t }
/// { ? }           Kill(p)                     { u p }
/// { }             Constant (t, k)             { e t }
/// { }             Nop                         { }
/// { e t1, e t2}   Binop(op, flag, t1, t2, t3) { e t3 }
///
/// Open questions:
///     StorageDead/StorageLive effects?
///     Where might wands be applied?
///         Owned vs borrowed values?
///      
///
///
/// Example translations:
///
/// (1)     Assign(_4, Use(Copy(_6.f)))
///             (where _6.f is a shared reference to a Copy type)
///     ==> { ? }               Kill(_4)                    { u _4 }
///         { s _6.f }          Duplicate(_6.f, temp1, mut) { s _6.f, e temp1 }
///         { u _4, e temp1 }   Set(_4, temp1, Mut)         { e _4 }
///
///     ==> Preconditions for the whole statment:
///             ? (conditions in order to kill _4, computed later)
///             s _6.f
///          
///         Postconditions for the whole statement
///             e _4
///             s _6.f
///     
///         Translation can be strengthened into the pre/post conditions for the whole statement
///         in a straightfoward way using the frame rule. Note that the pre/post conditions match
///         between statements.
///         
///             { ?, s _6.f }
///                 Kill(_4)
///             { u _4, s _6.f }
///                 Duplicate(_6.f, temp1, mut)
///             { u _4, s _6.f, e temp1 }
///                 Set(_4, temp1, Mut)
///             { e _4, s _6.f }
///
///
/// (2)     Assign(_2.f, CheckedBinaryOp(Add), Constant(5), Move(_7.g))
///
///     ==> { ? }                   Kill(_2.f)                               { u _2.f }
///         { e _7.g }              Move(_7.g, temp1)                        { u _7.g, e temp1 }
///         { }                     Constant(5, temp2)                       { e temp2 }
///         { e temp1, e temp2 }    BinOp (Add, true, temp1, temp2, temp3)   { e temp3 }
///         { e temp3, u _2.f }     Set (temp3, _2.f, Mut)                   { e _2.f }
///
///     ==> Combined translation by framing
///
///         { ?, e _7.g }
///             Kill(_2.f)
///         { u _2.f, e _7.g }
///             Move(_7.g, temp1)
///         { u _2.f, u _7.g, e temp1}
///             Constant(5, temp2)
///         { u _2.f, u _7.g, e temp1, e temp2}
///             BinOp (Add, true, temp1, temp2, temp3)
///         { u _7.g, u _2.f, e temp3 }
///             Set (temp3, _2.f, Mut)
///         { u _7.g, e _2.f }
///
impl<'tcx> MicroMirStatement<'tcx> {
    /// Read off the precondition for the core memory safety proof
    pub fn core_precondition(&self) -> Option<FxHashSet<PCSPermission>> {
        match self {
            _ => todo!(),
        }
    }

    pub fn core_postcondition(&self) -> Option<FxHashSet<PCSPermission>> {
        match self {
            _ => todo!(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PCSPermissionKind {
    Shared,
    Exclusive,
    Uninit,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PermissionTarget<'tcx> {
    Mir(Place<'tcx>),
    Tmp(TemporaryPlace),
}

impl<'tcx> From<Place<'tcx>> for PermissionTarget<'tcx> {
    fn from(p: Place<'tcx>) -> Self {
        PermissionTarget::Mir(p)
    }
}

impl<'tcx> From<TemporaryPlace> for PermissionTarget<'tcx> {
    fn from(t: TemporaryPlace) -> Self {
        PermissionTarget::Tmp(t)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PCSPermission<'tcx> {
    target: PermissionTarget<'tcx>,
    kind: PCSPermissionKind,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Mutability {
    Mut,
    Not,
}

impl<'tcx> PCSPermission<'tcx> {
    pub fn new_initialized(m: Mutability, target: PermissionTarget<'tcx>) -> Self {
        match m {
            Mutability::Mut => PCSPermission {
                target,
                kind: PCSPermissionKind::Exclusive,
            },
            Mutability::Not => PCSPermission {
                target,
                kind: PCSPermissionKind::Shared,
            },
        }
    }

    pub fn new_uninit(target: PermissionTarget<'tcx>) -> Self {
        PCSPermission {
            target,
            kind: PCSPermissionKind::Uninit,
        }
    }
}

pub fn init_analysis() {}

// TODO ITEMS:
//   Prefix invariant in init semantics
//   Operational translation
//   Calling the conditional analysis (refactored for operational MIR)
//   Kill elaboration into MicroMir
