// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{common::identifier::WithIdentifier, enum_predicate, legacy::ast::*};
use std::{collections::HashSet, fmt};

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

impl Predicate {
    /// A helper for constructing the predicate's `self` argument.
    pub fn construct_this(typ: Type) -> LocalVar {
        LocalVar::new("self", typ)
    }
    /// Construct a new abstract predicate of the given type.
    pub fn new_abstract(typ: Type) -> Predicate {
        let predicate_name = typ.name();
        Predicate::Struct(StructPredicate {
            name: predicate_name,
            this: Self::construct_this(typ),
            body: None,
        })
    }
    /// Is this predicate abstract.
    pub fn is_abstract(&self) -> bool {
        matches!(self, Predicate::Struct(StructPredicate { body: None, .. }))
    }
    /// Construct a new predicate that represents a type that models a primitive
    /// value such as an integer or a boolean.
    pub fn new_primitive_value(
        typ: Type,
        field: Field,
        bounds: Option<(Expr, Expr)>,
        is_unsigned: bool,
    ) -> Predicate {
        let predicate_name = typ.name();
        let this = Self::construct_this(typ);
        let val_field = Expr::from(this.clone()).field(field);
        let perm = Expr::acc_permission(val_field.clone(), PermAmount::Write);
        let mut conjuncts = vec![perm];
        if let Some((lower, upper)) = bounds {
            conjuncts.push(Expr::le_cmp(lower, val_field.clone()));
            conjuncts.push(Expr::le_cmp(val_field, upper));
        } else if is_unsigned {
            conjuncts.push(Expr::le_cmp(0.into(), val_field));
        };
        let body = conjuncts.into_iter().conjoin();
        Predicate::Struct(StructPredicate {
            name: predicate_name,
            this,
            body: Some(body),
        })
    }
    /// Construct a predicate that corresponds to a composite type that has only one variant such
    /// as `struct` or `tuple`.
    pub fn new_struct(typ: Type, fields: Vec<Field>) -> Predicate {
        Predicate::Struct(StructPredicate::new(typ, fields))
    }
    /// Construct a predicate that corresponds to a composite type that has zero or more than one
    /// variants.
    pub fn new_enum(
        this: LocalVar,
        discriminant_field: Field,
        discriminant_bounds: Expr,
        variants: Vec<(Expr, String, StructPredicate)>,
    ) -> Predicate {
        let predicate_name = this.typ.name();
        debug_assert!(
            variants
                .iter()
                .map(|(_, name, _)| name.to_string())
                .collect::<HashSet<_>>()
                .len()
                == variants.len()
        );
        Predicate::Enum(EnumPredicate {
            name: predicate_name,
            this,
            discriminant_field,
            discriminant_bounds,
            variants,
        })
    }
    /// A `self` place getter.
    pub fn self_place(&self) -> Expr {
        match self {
            Predicate::Struct(p) => p.this.clone().into(),
            Predicate::Enum(p) => p.this.clone().into(),
            Predicate::Bodyless(_, this) => this.clone().into(),
        }
    }
    /// The predicate name getter.
    pub fn name(&self) -> &str {
        match self {
            Predicate::Struct(p) => &p.name,
            Predicate::Enum(p) => &p.name,
            Predicate::Bodyless(ref name, _) => name,
        }
    }
    pub fn body(&self) -> Option<Expr> {
        match self {
            Predicate::Struct(struct_predicate) => struct_predicate.body.clone(),
            Predicate::Enum(enum_predicate) => Some(enum_predicate.body()),
            Predicate::Bodyless(_, _) => None,
        }
    }
}

impl WithIdentifier for Predicate {
    fn get_identifier(&self) -> String {
        match self {
            Predicate::Struct(p) => p.get_identifier(),
            Predicate::Enum(p) => p.get_identifier(),
            Predicate::Bodyless(name, _) => name.clone(),
        }
    }
}

/// The predicate for types that have exactly one variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

impl StructPredicate {
    pub fn new(typ: Type, fields: Vec<Field>) -> Self {
        let predicate_name = typ.name();
        let this = Predicate::construct_this(typ);
        let body = fields
            .into_iter()
            .flat_map(|field| {
                let predicate_name = field.typed_ref_name().unwrap();
                let location: Expr = Expr::from(this.clone()).field(field);
                let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
                let pred_perm =
                    Expr::predicate_access_predicate(predicate_name, location, PermAmount::Write);
                vec![field_perm, pred_perm]
            })
            .conjoin();
        Self {
            name: predicate_name,
            this,
            body: Some(body),
        }
    }
    /// Construct a predicate access predicate for this predicate.
    pub fn construct_access(&self, this: Expr, perm_amount: PermAmount) -> Expr {
        Expr::PredicateAccessPredicate(
            self.name.clone(),
            box this,
            perm_amount,
            Position::default(),
        )
    }
    /// Is the predicate's body just `true`?
    pub fn has_empty_body(&self) -> bool {
        matches!(self.body, Some(Expr::Const(Const::Bool(true), _)))
    }
}

impl WithIdentifier for StructPredicate {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

/// The predicate for types that have 0 or more than one variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct EnumVariantIndex(String);
pub type MaybeEnumVariantIndex = Option<EnumVariantIndex>;

impl EnumVariantIndex {
    pub fn get_variant_name(&self) -> &str {
        &self.0
    }

    pub fn new(s: String) -> Self {
        EnumVariantIndex(s)
    }
}

impl<'a> From<&'a Field> for EnumVariantIndex {
    fn from(field: &'a Field) -> Self {
        // TODO: Refactor to avoid string manipulations.
        assert!(field.name.starts_with("enum_"));
        EnumVariantIndex(field.name[5..].to_string())
    }
}

impl fmt::Display for EnumPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "enum_predicate {}({}){{", self.name, self.this)?;
        writeln!(f, "  discriminant_field={}", self.discriminant_field)?;
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

impl EnumPredicate {
    /// Construct an expression that represents the body of this predicate.
    pub fn body(&self) -> Expr {
        enum_predicate!(self)
    }
}

impl WithIdentifier for EnumPredicate {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
