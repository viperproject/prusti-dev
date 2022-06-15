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
/// { e t, u q }            Set(t, q, Mut)              { e q }
/// { s t, u q }            Set(t, q, Not)              { s q }
/// { e p }                 Move(p, t)                  { u p, e t }
/// { e p }                 Duplicate(p, t, Mut)        { e p, e t }
/// { s p }                 Duplicate(p, t, Not)        { s p, e t }
/// { ? }                   Kill(p)                     { u p }
/// { }                     Constant (t, k)             { e t }
/// { e t1, e t2 }          BinOp(op, flag, t1, t2, t3) { e t3 }
/// { e t1 }                UnOp(op, t1, t2)            { e t2 }
/// { }                     NullOp(op, t1)              { e t1 }
/// { }                     Nop                         { }
/// { m p0 }                Len(p0, t, Mut)             { e p0, e t}
/// { s p0 }                Len(p0, t, Not)             { s p0, e t}
///
/// encoding MIR Terminators
/// { }                     Goto(bb)                    { }
/// { e/s t }               SwitchInt(t, SwitchTargets) { e/s t }
///
///
///
///
///
///
///
/// WIP: Calls:
///
//// { e/s tf, [e/s ts] }    DoCall(tf, [tis])           { e _0 }    ** These definitely include wand operations too
///     tf      := temporary resource for function name
///     ts      := temporary resource for arguments
///             TODO: Is return place uninitialized before, or after the call? What if it alises an argument?
///                     I'm assuming after, but leaving the design open to either (yay microcode flexibility :) )
///     For calls that definitely diverge (destination is None) assert False afterwards.
///     For calls that do not, move _0 to the destination place, and GOTO the destination block.
/// { e _0 }                Return(bb)                  { assert false }
///
///
///
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
///                 Duplicate(_6.f, temp1, Mut)
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
///             { ?, e _7.g }
///                 Kill(_2.f)
///             { u _2.f, e _7.g }
///                 Move(_7.g, temp1)
///             { u _2.f, u _7.g, e temp1}
///                 Constant(5, temp2)
///             { u _2.f, u _7.g, e temp1, e temp2}
///                 BinOp (Add, true, temp1, temp2, temp3)
///             { u _7.g, u _2.f, e temp3 }
///                 Set (temp3, _2.f, Mut)
///             { u _7.g, e _2.f }
///
///
///
///
/// (3)     Call(Copy(_1), Vec<Copy(_2), Move(_3.f), Constant(10_u32)), Some<(_8, bbx)>, _, _, _)
///     ==> { e _1 }            Duplicate(_1, tf, Mut)      { e _1, e tf }
///         { e _2 }            Move(_2, t0, Mut)           { e t0 }
///         { e _3.f }          Move(_3.f, t1, Not)         { e t1 }
///         { }                 Constant(10, t2)            { e t2 }
///         { e t0, e t1, e t2, e t3 }
///                             DoCall(t0, Vec<t1, t2, t3>) { e _0 }
///
///         { ? }               Kill(_8)                    { u _8 }
///         { e _0 }            Move(_0, tmp1, Mut)         { u _0, e tmp1 } <-- should this be copy? What happens to _0?
///         { u _8, e tmp1}     Set(tmp1, _8)               { e _8 }
///
///
///     Framing of the whole statement:
///             { e _1, e _2, e _3.f }
///                 Duplicate(_1, tf, Mut)
///             { e _1, e _2, e tf, e _3.f }
///                 Move(_2, t0, Mut)
///             { e _1, e t0, e tf, e _3.f }
///                 Move(_3.f, t1, Not)         
///             { e _1, e t0, e tf, e t1 }
///                 Constant(10, t2)
///             { e _1, e t0, e tf, e t1, e t2 }
///                 Call(t0, Vec<t1, t2, t3>)
///             { e _1, e _0 }
///
///             { ?, e _0 }
///                 Kill(_8)
///             { u _8, e _0 }
///                 Move(_0, tmp1)
///             { u _8, u _0, e tmp1 }
///                 Set(tmp1, _8)
///             { u _0, e _8 }
///
///
///
///
/// WIP statements (not completely convinced about anything below here yet)
///     Q: Exiting the PCS also happens with wands... same underlying mechanic?
///
///
///
///
///
///
/// Open questions:
///     Untranslated MIR statements and RHS cases:
///         - (RHS) Repeat
///         - (RHS) Ref
///         - (RHS) ThreadLocalRef
///         - (RHS) AddressOf
///         - (RHS) Cast
///         - (RHS) Discriminant
///         - (RHS) Aggregate
///         - (RHS) ShallowInitBox
///         - Deinit (Just kill? should it retain the permission u p? Is it always followed by a StorageDead? )
///         - CopyNonOverlapping
///     AFAIK The following MIR statements do not change the PCS. Do we need them, or can they be special no-ops?
///         - FakeRead
///         - SetDiscriminant (how is this "used for drop elaboration", again?)
///         - Retag (it's for stacked borrows)
///         - AscribeUserType
///         - Coverage
///     Where might wands be applied?
///         Owned vs borrowed values?
///     Can we do our MaybeInit analysis on this?
///     Terminators:
///         Do we verify unwind paths?
///
///
///
///
///
/// WIP MIR Translations:
///     Hesitant because of this issue: https://github.com/rust-lang/rust/issues/68622
///     And also this
///          > These statements are not required. If the entire MIR body contains no
///            StorageLive/StorageDead statements for a particular local, the local is
///            always considered live.
///     Perhaps we should rely on our own iniaizliation analysis completely,
///         and treat these statements as no-ops.
///     StorageDead(p)      ->      { ? }       Kill(p)         { u p }
///                                 { u p }     Exit(p)         { }
///
///     StorageLive(p)      ->      { }         Enter(p)        { u p }
///         
///         The "enter" microcode op seems a lot like we could just specialize "kill"
///         Also, exiting the PCS can have wand-effects.
///
///
///     The permissions for Repeat:
///         If p is shared: always OK,
///         If p is exclusive (owned or borrowed) then one of
///             - k = 1
///             - k = 0
///             - p is Clone (this implies p is owned since &mut T is *never* Clone)
///         We are not allowed to move out of arrays, values must be copied out.
///             - In mut arrays, we're allowed to overwrite the entire array
///             - We're also allowed to overwrite individual elements
///             - Elements can be read and shared borrowed but not mutably borrowed or moved.
///
///     Repeat(p, k)        ->      { ... p }       ...             { ... tmp1 }    Get the Operand permission, must be copy
///                                 { e/s tmp1 }    Many(tmp1, l)   { e tmp2 }      Whole array is owned
///                                                                                 Delegate to unpack????????????
///     This needs more thought, and probably a theory for structs with shared fields before
///     we can model this operation
///
///
///
///
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
