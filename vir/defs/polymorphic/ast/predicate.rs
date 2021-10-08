// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::polymorphic::ast::*;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Predicate {
    Struct(StructPredicate),
    Enum(EnumPredicate),
    Bodyless(Type, LocalVar),
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
        Predicate::Struct(StructPredicate {
            typ: typ.clone(),
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
        let this = Self::construct_this(typ.clone());
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
            typ,
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
        debug_assert!(
            variants
                .iter()
                .map(|(_, name, _)| name.to_string())
                .collect::<HashSet<_>>()
                .len()
                == variants.len()
        );
        Predicate::Enum(EnumPredicate {
            typ: this.typ.clone(),
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
    /// The predicate type getter.
    pub fn get_type(&self) -> &Type {
        match self {
            Predicate::Struct(p) => &p.typ,
            Predicate::Enum(p) => &p.typ,
            Predicate::Bodyless(typ, _) => typ,
        }
    }
    /// The predicate name getter.
    pub fn name(&self) -> String {
        match self {
            Predicate::Struct(p) => p.typ.name(),
            Predicate::Enum(p) => p.typ.name(),
            Predicate::Bodyless(ref typ, _) => typ.name(),
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
            Predicate::Bodyless(typ, _) => typ.encode_as_string(),
        }
    }
}

/// The predicate for types that have exactly one variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StructPredicate {
    /// The predicate name in Viper.
    pub typ: Type,
    /// The self reference.
    pub this: LocalVar,
    /// The optional body of the predicate.
    pub body: Option<Expr>,
}

impl fmt::Display for StructPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "struct_predicate {}({}",
            self.typ.encode_as_string(),
            self.this
        )?;
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
        let this = Predicate::construct_this(typ.clone());
        let body = fields
            .into_iter()
            .flat_map(|field| {
                let location: Expr = Expr::from(this.clone()).field(field.clone());
                let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
                let pred_perm =
                    Expr::predicate_access_predicate(field.typ, location, PermAmount::Write);
                vec![field_perm, pred_perm]
            })
            .conjoin();
        Self {
            typ,
            this,
            body: Some(body),
        }
    }
    /// Construct a predicate access predicate for this predicate.
    pub fn construct_access(&self, this: Expr, perm_amount: PermAmount) -> Expr {
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type: self.typ.clone(),
            argument: Box::new(this),
            permission: perm_amount,
            position: Position::default(),
        })
    }
    /// Is the predicate's body just `true`?
    pub fn has_empty_body(&self) -> bool {
        matches!(
            self.body,
            Some(Expr::Const(ConstExpr {
                value: Const::Bool(true),
                ..
            }))
        )
    }
}

impl WithIdentifier for StructPredicate {
    fn get_identifier(&self) -> String {
        self.typ.encode_as_string()
    }
}

/// The predicate for types that have 0 or more than one variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumPredicate {
    /// The predicate name in Viper.
    pub typ: Type,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EnumVariantIndex(pub(crate) String);

impl EnumVariantIndex {
    pub fn get_variant_name(&self) -> &str {
        &self.0
    }

    pub fn new(s: String) -> Self {
        EnumVariantIndex(s)
    }
}

pub type MaybeEnumVariantIndex = Option<EnumVariantIndex>;

impl<'a> From<&'a Field> for EnumVariantIndex {
    fn from(field: &'a Field) -> Self {
        // TODO: Refactor to avoid string manipulations.
        assert!(field.name.starts_with("enum_"));
        Self(field.name[5..].to_string())
    }
}

impl fmt::Display for EnumPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "enum_predicate {}({}){{", self.typ.name(), self.this)?;
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
        let discriminant_loc = Expr::from(self.this.clone()).field(self.discriminant_field.clone());
        let discriminant_perm = Expr::acc_permission(discriminant_loc, PermAmount::Write);
        let mut parts = vec![discriminant_perm, self.discriminant_bounds.clone()];
        for (guard, name, variant) in self.variants.iter() {
            if variant.has_empty_body() {
                continue;
            }
            let field = Field::new(format!("enum_{}", name), variant.this.typ.clone());
            let location: Expr = Expr::from(self.this.clone()).field(field);
            let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
            let pred_perm = variant.construct_access(location, PermAmount::Write);
            parts.push(Expr::and(
                field_perm,
                Expr::implies(guard.clone(), pred_perm),
            ));
        }
        parts.into_iter().conjoin()
    }
}

impl WithIdentifier for EnumPredicate {
    fn get_identifier(&self) -> String {
        self.typ.name()
    }
}
