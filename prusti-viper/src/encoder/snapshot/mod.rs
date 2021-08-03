// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty;
use prusti_common::vir;
use prusti_common::vir::{Expr, Type};
use std::collections::HashMap;

pub mod encoder;
mod patcher;

/// Snapshot of a VIR type. This enum is internal to the snapshot encoding and
/// should not need to be exposed to the encoder in general.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone)]
enum Snapshot {
    /// Corresponds directly to an existing Viper type.
    Primitive(Type),
    /// Encodes types with no content; these need not be provided as arguments
    /// to snapshot constructors.
    Unit,
    /// Encodes a complex type: tuples, ADTs, or closures.
    Complex {
        predicate_name: String,
        domain: String,
        discriminant_func: vir::DomainFunc,
        snap_func: vir::FunctionIdentifier,
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
        predicate_name: String,
        domain: String,
        snap_func: vir::FunctionIdentifier,
        slice_helper: vir::FunctionIdentifier,
        cons: vir::DomainFunc,
        read: vir::DomainFunc,
    },
    /// Slices
    Slice {
        predicate_name: String,
        domain: String,
        snap_func: vir::FunctionIdentifier,
        /// Collect a slice snapshot from an impure context using lookup_pure calls until we have
        /// Slice$len(self) elements in the result Seq[elem_ty]
        slice_collect_func: vir::FunctionIdentifier,
        /// This slice snapshot is being sliced, so we collect elements using read from self in the
        /// result Seq[elem_ty]
        slice_helper: vir::FunctionIdentifier,
        cons: vir::DomainFunc,
        read: vir::DomainFunc,
        len: vir::DomainFunc,
    },
    /// Type cannot be encoded: type parameters, unsupported types.
    Abstract {
        predicate_name: String,
        domain: String,
        snap_func: vir::FunctionIdentifier,
    },

    /// A type which will be resolved to a different snapshot kind.
    /// (Should only appear while encoding is in progress!)
    Lazy(Type),
}

impl Snapshot {
    pub fn get_type(&self) -> Type {
        match self {
            Self::Primitive(ty) => ty.clone(),
            Self::Unit => Type::Domain(encoder::UNIT_DOMAIN_NAME.to_string()),
            Self::Complex { predicate_name, .. }
            | Self::Abstract { predicate_name, .. }
            | Self::Array { predicate_name, .. }
            | Self::Slice { predicate_name, .. } => Type::Snapshot(predicate_name.to_string()),
            Self::Lazy(ty) => ty.clone(),
        }
    }

    pub fn is_quantifiable(&self) -> bool {
        // TODO: allow more types?
        match self {
            Self::Primitive(_) => true,
            _ => false,
        }
    }

    pub fn supports_equality(&self) -> bool {
        use Snapshot::*;
        matches!(self, Primitive(_) | Unit | Complex { .. } | Array { .. } | Slice { .. })
    }
}
