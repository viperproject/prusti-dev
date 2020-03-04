// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::ast::*;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Predicate {
    Struct(StructPredicate),
    Enum(EnumPredicate),
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Predicate::Struct(p) => write!(f, "{}", p),
            Predicate::Enum(p) => write!(f, "{}", p),
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
        match self {
            Predicate::Struct(StructPredicate { body: None, .. }) => true,
            _ => false,
        }
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
            this: this,
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
        discriminant: Expr,
        discriminant_bounds: Expr,
        variants: Vec<(Expr, String, StructPredicate)>,
    ) -> Predicate {
        let predicate_name = this.typ.name();
        Predicate::Enum(EnumPredicate {
            name: predicate_name,
            this: this,
            discriminant: discriminant,
            discriminant_bounds: discriminant_bounds,
            variants: variants,
        })
    }
    /// Construct a new predicate that represents an array or a slice
    pub fn new_slice_or_array(
        typ: Type,
        elem_field: Field,
        array_field: Field,
        len: Option<u64>,
    ) -> Predicate {
        let predicate_name = typ.name();
        let this = Self::construct_this(typ);
        // self.val_array
        let val_field = Expr::from(this.clone()).field(array_field);
        // acc(self.val_array)
        let val_field_acc = Expr::acc_permission(val_field.clone(), PermAmount::Write);
        // forall i: Int :: { self.val_array[i] } 0 <= i < |self.val_array| ==> acc(self.val_array[i].val_*)
        let elems_acc = {
            let idx_local = LocalVar::new("i", Type::Int);
            let idx = Expr::local(idx_local.clone());
            // 0 <= i < |self.val_array|
            let idx_bounds = Expr::and(
                Expr::le_cmp(Expr::Const(Const::Int(0), Position::default()), idx.clone()),
                Expr::lt_cmp(idx.clone(), Expr::seq_len(val_field.clone()))
            );
            // self.val_array[i]
            let elems_acc = Expr::seq_index(val_field.clone(), idx.clone());
            let elems_acc_field = ResourceAccess::FieldAccessPredicate(FieldAccessPredicate {
                // self.val_array[i].val_*
                place: box Expr::field(elems_acc.clone(), elem_field),
                perm: PermAmount::Write
            });
            Expr::CondResourceAccess(
                CondResourceAccess {
                    vars: vec![idx_local],
                    triggers: vec![Trigger::new(vec![elems_acc])],
                    cond: box idx_bounds,
                    resource: elems_acc_field,
                },
                Position::default()
            )
        };
        // Combining everything, and specifying the size of the array if it is known
        let body = {
            if let Some(len) = len {
                // |self.val_array| == len
                let len_is = Expr::eq_cmp(
                    Expr::seq_len(val_field),
                    Expr::Const(Const::BigInt(len.to_string()), Position::default())
                );
                Expr::and(val_field_acc, Expr::and(len_is, elems_acc))
            } else {
                Expr::and(val_field_acc, elems_acc)
            }
        };

        Predicate::Struct(StructPredicate {
            name: predicate_name,
            this,
            body: Some(body),
        })
    }
    /// A `self` place getter.
    pub fn self_place(&self) -> Expr {
        match self {
            Predicate::Struct(p) => p.this.clone().into(),
            Predicate::Enum(p) => p.this.clone().into(),
        }
    }
    /// The predicate name getter.
    pub fn name(&self) -> &str {
        match self {
            Predicate::Struct(p) => &p.name,
            Predicate::Enum(p) => &p.name,
        }
    }
}

impl WithIdentifier for Predicate {
    fn get_identifier(&self) -> String {
        match self {
            Predicate::Struct(p) => p.get_identifier(),
            Predicate::Enum(p) => p.get_identifier(),
        }
    }
}

/// The predicate for types that have exactly one variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
                let location: Expr = Expr::from(this.clone()).field(field).into();
                let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
                let pred_perm =
                    Expr::predicate_access_predicate(predicate_name, location, PermAmount::Write);
                vec![field_perm, pred_perm]
            })
            .conjoin();
        Self {
            name: predicate_name,
            this: this,
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
        match self.body {
            Some(Expr::Const(Const::Bool(true), _)) => true,
            _ => false,
        }
    }
}

impl WithIdentifier for StructPredicate {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

/// The predicate for types that have 0 or more than one variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumPredicate {
    /// The predicate name in Viper.
    pub name: String,
    /// The self reference.
    pub this: LocalVar,
    /// The discriminant field.
    pub discriminant: Expr,
    /// The restrictions of the discriminant field.
    pub discriminant_bounds: Expr,
    /// `(guard, variant_name, variant_predicate)` of the enum. `guard`
    /// is a condition on `discriminant` under which this variant holds.
    pub variants: Vec<(Expr, String, StructPredicate)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnumVariantIndex(String);
pub type MaybeEnumVariantIndex = Option<EnumVariantIndex>;

impl EnumVariantIndex {
    pub fn get_variant_name(&self) -> &str {
        &self.0
    }
}

impl<'a> Into<EnumVariantIndex> for &'a Field {
    fn into(self) -> EnumVariantIndex {
        // TODO: Refactor to avoid string manipulations.
        assert!(self.name.starts_with("enum_"));
        EnumVariantIndex(self.name[5..].to_string())
    }
}

impl fmt::Display for EnumPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "enum_predicate {}({}){{\n", self.name, self.this)?;
        write!(f, "  discriminant={}\n", self.discriminant)?;
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
        let discriminant_perm = Expr::acc_permission(self.discriminant.clone(), PermAmount::Write);
        let mut parts = vec![discriminant_perm, self.discriminant_bounds.clone()];
        for (guard, name, variant) in self.variants.iter() {
            if variant.has_empty_body() {
                continue;
            }
            let field = Field::new(format!("enum_{}", name), variant.this.typ.clone());
            let location: Expr = Expr::from(self.this.clone()).field(field).into();
            let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
            let pred_perm = variant.construct_access(location, PermAmount::Write);
            parts.push(
                Expr::and(
                    field_perm,
                    Expr::implies(guard.clone(), pred_perm),
                )
            );
        }
        parts.into_iter().conjoin()
    }
}

impl WithIdentifier for EnumPredicate {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}
