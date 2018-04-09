// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


use rustc::mir;
use rustc::ty::Ty;

/// An abstraction over all local variables used in a procedure.
#[derive(Clone, Copy)]
pub enum Local {
    /// A local variable declared in MIR.
    RealLocal(mir::Local),
    /// A ghost interned local variable created to simplify translation.
    /// Variables of this type resembles real Rust local variables.
    GhostLocal(u32),
    /// A ghost interned local variable created for keeping track of the
    /// ghost state on the Viper level.
    PureGhostLocal(u32),
}

/// Declaration of a ghost local variable.
pub struct GhostLocalDecl<'tcx> {
    name: String,
    ty: Ty<'tcx>,
}

/// Type of a Viper ghost variable.
pub enum PureViperType {
    Bool,
    Int,
    Ref,
}

/// Declaration of a pure ghost variable.
pub struct PureGhostLocalDecl {
    name: String,
    ty: PureViperType,
}

/// This place is a generalisation of mir::Place.
pub enum Place<'tcx> {
    /// A place that is a local variable.
    Local(Local),
    /// A place that is a MIR place.
    Place(mir::Place<'tcx>),
    /// A place that is a MIR place starting at a specific local variable
    /// instead of its normal root.
    ///
    /// For example, if `substituted_root = _g5` and
    /// `place = _3.f`, then in Viper this place would be encoded as
    /// `_g5.val_ref.T$f.val_ref`
    SubstitutedPlace {
        substituted_root: Local,
        place: mir::Place<'tcx>,
    },
}
