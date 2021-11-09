// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty;
use std::collections::HashMap;
use vir_crate::polymorphic::{self as vir, Expr, Type};

/// Snapshot of a VIR type. This enum is internal to the snapshot encoding and
/// should not need to be exposed to the encoder in general.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone)]
pub(super) enum Snapshot {
    /// Corresponds directly to an existing Viper type.
    Primitive(Type),
    /// Encodes a complex type: tuples, ADTs, or closures.
    Complex {
        predicate_type: Type,
        _domain: String,
        discriminant_func: vir::DomainFunc,
        _snap_func: vir::FunctionIdentifier,
        /// [variants] has one entry for tuples, structs, and closures.
        /// For enums, it has as many entries as there are variants.
        /// The first function is the constructor, the hashmap encodes the
        /// field access functions, keyed by their name.
        variants: Vec<(vir::DomainFunc, HashMap<String, vir::DomainFunc>)>,
        /// Mapping of variant names (as used by Prusti) to variant indices
        /// in the [variants] vector. Empty for non-enums.
        variant_names: HashMap<String, usize>,
    }, // TODO: separate variant for enums and one-variant Complexes?
    /// Arrays
    Array {
        predicate_type: Type,
        _domain: String,
        _snap_func: vir::FunctionIdentifier,
        slice_helper: vir::FunctionIdentifier,
        cons: vir::DomainFunc,
        read: vir::DomainFunc,
    },
    /// Slices
    Slice {
        predicate_type: Type,
        _domain: String,
        _snap_func: vir::FunctionIdentifier,
        /// Collect a slice snapshot from an impure context using lookup_pure calls until we have
        /// Slice$len(self) elements in the result Seq[elem_ty]
        _slice_collect_func: vir::FunctionIdentifier,
        /// This slice snapshot is being sliced, so we collect elements using read from self in the
        /// result Seq[elem_ty]
        slice_helper: vir::FunctionIdentifier,
        cons: vir::DomainFunc,
        read: vir::DomainFunc,
        len: vir::DomainFunc,
    },
    /// Type cannot be encoded: type parameters, unsupported types.
    Abstract {
        predicate_type: Type,
        _domain: String,
        _snap_func: vir::FunctionIdentifier,
    },

    /// A type which will be resolved to a different snapshot kind.
    /// (Should only appear while encoding is in progress!)
    Lazy(Type),
}

impl Snapshot {
    pub fn get_type(&self) -> Type {
        match self {
            Self::Primitive(ty) => ty.clone(),
            Self::Complex { predicate_type, .. }
            | Self::Abstract { predicate_type, .. }
            | Self::Array { predicate_type, .. }
            | Self::Slice { predicate_type, .. } => {
                assert!(predicate_type.is_snapshot());
                predicate_type.clone()
            }
            Self::Lazy(ty) => ty.clone(),
        }
    }

    pub fn is_quantifiable(&self) -> bool {
        // TODO: allow more types?
        matches!(self, Self::Primitive(_))
    }

    pub fn supports_equality(&self) -> bool {
        use Snapshot::*;
        matches!(
            self,
            Primitive(_) | Complex { .. } | Array { .. } | Slice { .. }
        )
    }
}
