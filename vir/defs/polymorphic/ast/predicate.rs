// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::polymorphic::ast::*;
use std::fmt;
use std::collections::{HashSet, HashMap};

use super::super::super::{legacy, converter};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Predicate {
    Struct(StructPredicate),
    Enum(EnumPredicate),
    Bodyless(String, LocalVar),
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Predicate::Struct(p) => write!(f, "{}", p),
            Predicate::Enum(p) => write!(f, "{}", p),
            Predicate::Bodyless(name, this) => write!(f, "bodyless_predicate {}({});", name, this),
        }
    }
}

impl From<Predicate> for legacy::Predicate {
    fn from(predicate: Predicate) -> legacy::Predicate {
        match predicate {
            Predicate::Struct(struct_predicate) => legacy::Predicate::Struct(legacy::StructPredicate::from(struct_predicate)),
            Predicate::Enum(enum_predicate) => legacy::Predicate::Enum(legacy::EnumPredicate::from(enum_predicate)),
            Predicate::Bodyless(label, local_var) => legacy::Predicate::Bodyless(label, legacy::LocalVar::from(local_var)),
        }
    }
}

impl converter::Generic for Predicate {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        match self {
            Predicate::Struct(struct_predicate) => Predicate::Struct(struct_predicate.substitute(map)),
            Predicate::Enum(enum_predicate) => Predicate::Enum(enum_predicate.substitute(map)),
            Predicate::Bodyless(label, local_var) => Predicate::Bodyless(label, local_var.substitute(map)),
        }
    }
}

/// The predicate for types that have exactly one variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StructPredicate {
    /// The predicate name in Viper.
    pub name: String,
    /// The self reference.
    pub this: LocalVar,
    /// The optional body of the predicate.
    pub body: Option<Expr>,
}

impl fmt::Display for StructPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "struct_predicate {}({}", self.name, self.this)?;
        match self.body {
            None => writeln!(f, ");"),
            Some(ref body) => {
                writeln!(f, "){{")?;
                writeln!(f, "  {}", body)?;
                writeln!(f, "}}")
            }
        }
    }
}

impl From<StructPredicate> for legacy::StructPredicate {
    fn from(struct_predicate: StructPredicate) -> legacy::StructPredicate {
        legacy::StructPredicate {
            name: struct_predicate.name,
            this: legacy::LocalVar::from(struct_predicate.this),
            body: struct_predicate.body.map(|body_expr| legacy::Expr::from(body_expr)),
        }
    }
}

impl converter::Generic for StructPredicate {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut struct_predicate = self;
        struct_predicate.this = struct_predicate.this.substitute(map);
        struct_predicate.body = struct_predicate.body.map(|expr| expr.substitute(map));
        struct_predicate
    }
}

/// The predicate for types that have 0 or more than one variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumPredicate {
    /// The predicate name in Viper.
    pub name: String,
    /// The self reference.
    pub this: LocalVar,
    /// The discriminant field.
    pub discriminant_field: Field,
    /// The restrictions of the discriminant field.
    pub discriminant_bounds: Expr,
    /// `(guard, variant_name, variant_predicate)` of the enum. `guard`
    /// is a condition on `discriminant` under which this variant holds.
    pub variants: Vec<(Expr, String, StructPredicate)>,
}

impl From<EnumPredicate> for legacy::EnumPredicate {
    fn from(enum_predicate: EnumPredicate) -> legacy::EnumPredicate {
        legacy::EnumPredicate {
            name: enum_predicate.name,
            this: legacy::LocalVar::from(enum_predicate.this),
            discriminant_field: legacy::Field::from(enum_predicate.discriminant_field),
            discriminant_bounds: legacy::Expr::from(enum_predicate.discriminant_bounds),
            variants: enum_predicate.variants.into_iter().map(|(expr, label, struct_predicate)| (legacy::Expr::from(expr), label, legacy::StructPredicate::from(struct_predicate))).collect(),
        }
    }
}

impl converter::Generic for EnumPredicate {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut enum_predicate = self;
        enum_predicate.this = enum_predicate.this.substitute(map);
        enum_predicate.discriminant_field = enum_predicate.discriminant_field.substitute(map);
        enum_predicate.discriminant_bounds = enum_predicate.discriminant_bounds.substitute(map);
        enum_predicate.variants = enum_predicate.variants.into_iter().map(|(expr, label, struct_predicate)| (expr.substitute(map), label, struct_predicate.substitute(map))).collect();
        enum_predicate
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumVariantIndex(String);

impl EnumVariantIndex {
    pub fn get_variant_name(&self) -> &str {
        &self.0
    }

    pub fn new(s: String) -> Self {
        EnumVariantIndex(s)
    }
}

impl From<EnumVariantIndex> for legacy::EnumVariantIndex {
    fn from(enum_variant_index: EnumVariantIndex) -> legacy::EnumVariantIndex {
        legacy::EnumVariantIndex::new(enum_variant_index.0)
    }
}

impl converter::Generic for EnumVariantIndex {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
    }
}

pub type MaybeEnumVariantIndex = Option<EnumVariantIndex>;

impl fmt::Display for EnumPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "enum_predicate {}({}){{\n", self.name, self.this)?;
        write!(f, "  discriminant_field={}\n", self.discriminant_field)?;
        for (guard, name, variant) in self.variants.iter() {
            writeln!(f, "  {}: {} ==> {}\n", name, guard, variant)?;
        }
        writeln!(f, "}}")
    }
}

impl fmt::Display for EnumVariantIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{{}}}", self.0)
    }
}
