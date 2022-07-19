// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::borrows::Borrow;
use crate::{common::display, converter::type_substitution::Generic, polymorphic::ast::*};
use rustc_hash::FxHashMap;
use std::{
    fmt,
    hash::{Hash, Hasher},
    mem,
    mem::discriminant,
};

#[derive(
    Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord,
)]
pub enum Expr {
    /// A local var
    Local(Local),
    /// An enum variant: base, variant index.
    Variant(Variant),
    /// A field access
    Field(FieldExpr),
    /// The inverse of a `val_ref` field access
    AddrOf(AddrOf),
    LabelledOld(LabelledOld),
    Const(ConstExpr),
    /// lhs, rhs, borrow, position
    MagicWand(MagicWand),
    /// PredicateAccessPredicate: predicate_type, arg, permission amount
    PredicateAccessPredicate(PredicateAccessPredicate),
    FieldAccessPredicate(FieldAccessPredicate),
    UnaryOp(UnaryOp),
    BinOp(BinOp),
    /// Container Operation on a Viper container (e.g. Seq index)
    ContainerOp(ContainerOp),
    /// Viper Seq
    Seq(Seq),
    /// Viper Map
    Map(Map),
    /// Unfolding: predicate name, predicate_args, in_expr, permission amount, enum variant
    Unfolding(Unfolding),
    /// Cond: guard, then_expr, else_expr
    Cond(Cond),
    /// ForAll: variables, triggers, body
    ForAll(ForAll),
    /// Exists: variables, triggers, body
    Exists(Exists),
    /// let variable == (expr) in body
    LetExpr(LetExpr),
    /// FuncApp: function_name, args, formal_args, return_type, Viper position
    FuncApp(FuncApp),
    /// Domain function application: function_name, args, formal_args, return_type, domain_name, Viper position (unused)
    DomainFuncApp(DomainFuncApp),
    // TODO use version below once providing a return type is supported in silver
    // DomainFuncApp(String, Vec<Expr>, Vec<LocalVar>, Type, String, Position),
    /// Inhale Exhale: inhale expression, exhale expression, Viper position (unused)
    InhaleExhale(InhaleExhale),
    /// Inform the fold-unfold algorithm that at this program point a enum type can be downcasted
    /// to one of its variants. This statement is a no-op for Viper.
    /// Arguments:
    /// * expression in which the downcast is visible
    /// * place to the enumeration that is downcasted
    /// * field that encodes the variant
    Downcast(DowncastExpr),
    /// Snapshot call to convert from a Ref to a snapshot value
    SnapApp(SnapApp),
    /// Cast from one type into another.
    Cast(Cast),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Local(local) => local.fmt(f),
            Expr::Variant(variant) => variant.fmt(f),
            Expr::Field(field) => field.fmt(f),
            Expr::AddrOf(addr_of) => addr_of.fmt(f),
            Expr::Const(const_expr) => const_expr.fmt(f),
            Expr::LabelledOld(labelled_old) => labelled_old.fmt(f),
            Expr::MagicWand(magic_wand) => magic_wand.fmt(f),
            Expr::PredicateAccessPredicate(predicate_access_predicate) => {
                predicate_access_predicate.fmt(f)
            }
            Expr::FieldAccessPredicate(field_access_predicate) => field_access_predicate.fmt(f),
            Expr::UnaryOp(unary_op) => unary_op.fmt(f),
            Expr::BinOp(bin_op) => bin_op.fmt(f),
            Expr::Unfolding(unfolding) => unfolding.fmt(f),
            Expr::Cond(cond) => cond.fmt(f),
            Expr::ForAll(for_all) => for_all.fmt(f),
            Expr::Exists(exists) => exists.fmt(f),
            Expr::LetExpr(let_expr) => let_expr.fmt(f),
            Expr::FuncApp(func_app) => func_app.fmt(f),
            Expr::DomainFuncApp(domain_func_app) => domain_func_app.fmt(f),
            Expr::InhaleExhale(inhale_exhale) => inhale_exhale.fmt(f),
            Expr::SnapApp(snap_app) => snap_app.fmt(f),
            Expr::ContainerOp(container_op) => container_op.fmt(f),
            Expr::Seq(seq) => seq.fmt(f),
            Expr::Map(map) => map.fmt(f),
            Expr::Downcast(downcast_expr) => downcast_expr.fmt(f),
            Expr::Cast(expr) => expr.fmt(f),
        }
    }
}

macro_rules! __unary_op__ {
    ($($fn_name:ident $kind_name:ident),*) => {
        impl Expr {$(
            #[allow(clippy::should_implement_trait)]
            pub fn $fn_name(expr: Expr) -> Self {
                Expr::UnaryOp(UnaryOp {
                    op_kind: UnaryOpKind:: $kind_name,
                    argument: Box::new(expr),
                    position: Position::default(),
                })
            }
        )*}
    }
}

__unary_op__! {
    not Not,
    minus Minus
}

macro_rules! __binary_op__ {
    ($($fn_name:ident $kind_name:ident),*) => {
        impl Expr {$(
            #[allow(clippy::should_implement_trait)]
            pub fn $fn_name(left: Expr, right: Expr) -> Self {
                Expr::BinOp(BinOp {
                    op_kind: BinaryOpKind:: $kind_name,
                    left: Box::new(left),
                    right: Box::new(right),
                    position: Position::default(),
                })
            }
        )*}
    }
}

__binary_op__! {
    gt_cmp GtCmp,
    ge_cmp GeCmp,
    lt_cmp LtCmp,
    le_cmp LeCmp,
    eq_cmp EqCmp,
    add Add,
    sub Sub,
    mul Mul,
    div Div,
    modulo Mod,
    and And,
    or Or,
    implies Implies
}

impl Expr {
    pub fn pos(&self) -> Position {
        match self {
            Expr::Local(Local { position, .. })
            | Expr::Variant(Variant { position, .. })
            | Expr::Field(FieldExpr { position, .. })
            | Expr::AddrOf(AddrOf { position, .. })
            | Expr::Const(ConstExpr { position, .. })
            | Expr::LabelledOld(LabelledOld { position, .. })
            | Expr::MagicWand(MagicWand { position, .. })
            | Expr::PredicateAccessPredicate(PredicateAccessPredicate { position, .. })
            | Expr::FieldAccessPredicate(FieldAccessPredicate { position, .. })
            | Expr::UnaryOp(UnaryOp { position, .. })
            | Expr::BinOp(BinOp { position, .. })
            | Expr::Unfolding(Unfolding { position, .. })
            | Expr::Cond(Cond { position, .. })
            | Expr::ForAll(ForAll { position, .. })
            | Expr::Exists(Exists { position, .. })
            | Expr::LetExpr(LetExpr { position, .. })
            | Expr::FuncApp(FuncApp { position, .. })
            | Expr::DomainFuncApp(DomainFuncApp { position, .. })
            | Expr::InhaleExhale(InhaleExhale { position, .. })
            | Expr::SnapApp(SnapApp { position, .. })
            | Expr::ContainerOp(ContainerOp { position, .. })
            | Expr::Cast(Cast { position, .. })
            | Expr::Map(Map { position, .. })
            | Expr::Seq(Seq { position, .. }) => *position,
            Expr::Downcast(DowncastExpr { base, .. }) => base.pos(),
        }
    }

    #[must_use]
    pub fn set_pos(self, position: Position) -> Self {
        // a macro to update the position for all cases
        // it depends on the variants specific type to have the same name as the variant, except in the two special cases.
        macro_rules! __set_pos__ {
            ($($Variant:tt),*) => {
                match self {
                    $(Expr:: $Variant (inner) => Expr:: $Variant ($Variant {
                        position,
                        ..inner
                    }),)*
                    Expr::Field(inner) => Expr::Field(FieldExpr {
                        position,
                        ..inner
                    }),
                    Expr::Const(inner) => Expr::Const(ConstExpr {
                        position,
                        ..inner
                    }),
                    Expr::Downcast(..) => self,
                }
            }
        }

        __set_pos__!(
            Local,
            Variant,
            AddrOf,
            LabelledOld,
            MagicWand,
            PredicateAccessPredicate,
            FieldAccessPredicate,
            UnaryOp,
            BinOp,
            ContainerOp,
            Seq,
            Map,
            Unfolding,
            Cond,
            ForAll,
            Exists,
            LetExpr,
            FuncApp,
            DomainFuncApp,
            InhaleExhale,
            SnapApp,
            Cast
        )
    }

    // Replace all Position::default() positions with `pos`
    #[must_use]
    pub fn set_default_pos(self, pos: Position) -> Self {
        struct DefaultPosReplacer {
            new_pos: Position,
        }
        impl ExprFolder for DefaultPosReplacer {
            fn fold(&mut self, e: Expr) -> Expr {
                let expr = default_fold_expr(self, e);
                if expr.pos().is_default() {
                    expr.set_pos(self.new_pos)
                } else {
                    expr
                }
            }
        }
        DefaultPosReplacer { new_pos: pos }.fold(self)
    }

    pub fn predicate_access_predicate(predicate_type: Type, place: Expr, perm: PermAmount) -> Self {
        let pos = place.pos();
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type,
            argument: Box::new(place),
            permission: perm,
            position: pos,
        })
    }

    pub fn field_access_predicate(place: Expr, perm: PermAmount) -> Self {
        let pos = place.pos();
        Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(place),
            permission: perm,
            position: pos,
        })
    }

    pub fn pred_permission(place: Expr, perm: PermAmount) -> Option<Self> {
        let typ = place.get_type();
        if typ.is_typed_ref_or_type_var() || typ.is_seq() || typ.is_map() {
            Some(Expr::predicate_access_predicate(typ.clone(), place, perm))
        } else {
            None
        }
    }

    pub fn acc_permission(place: Expr, perm: PermAmount) -> Self {
        Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(place),
            permission: perm,
            position: Position::default(),
        })
    }

    pub fn labelled_old(label: &str, expr: Expr) -> Self {
        Expr::LabelledOld(LabelledOld {
            label: label.to_string(),
            base: Box::new(expr),
            position: Position::default(),
        })
    }

    pub fn bin_op(op_kind: BinaryOpKind, left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOp {
            op_kind,
            left: Box::new(left),
            right: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn ne_cmp(left: Expr, right: Expr) -> Self {
        Expr::not(Expr::eq_cmp(left, right))
    }

    #[allow(clippy::should_implement_trait)]
    /// Encode Rust reminder. This is *not* Viper modulo.
    pub fn rem(left: Expr, right: Expr) -> Self {
        let abs_right = Expr::ite(
            Expr::ge_cmp(right.clone(), 0.into()),
            right.clone(),
            Expr::minus(right.clone()),
        );
        Expr::ite(
            Expr::or(
                Expr::ge_cmp(left.clone(), 0.into()),
                Expr::eq_cmp(Expr::modulo(left.clone(), right.clone()), 0.into()),
            ),
            // positive value or left % right == 0
            Expr::modulo(left.clone(), right.clone()),
            // negative value
            Expr::sub(Expr::modulo(left, right), abs_right),
        )
    }

    pub fn xor(left: Expr, right: Expr) -> Self {
        Expr::not(Expr::eq_cmp(left, right))
    }

    pub fn forall(vars: Vec<LocalVar>, triggers: Vec<Trigger>, body: Expr) -> Self {
        assert!(
            !vars.is_empty(),
            "A quantifier must have at least one variable."
        );
        Expr::ForAll(ForAll {
            variables: vars,
            triggers,
            body: Box::new(body),
            position: Position::default(),
        })
    }

    pub fn exists(vars: Vec<LocalVar>, triggers: Vec<Trigger>, body: Expr) -> Self {
        assert!(
            !vars.is_empty(),
            "A quantifier must have at least one variable."
        );
        Expr::Exists(Exists {
            variables: vars,
            triggers,
            body: Box::new(body),
            position: Position::default(),
        })
    }

    pub fn ite(guard: Expr, left: Expr, right: Expr) -> Self {
        Expr::Cond(Cond {
            guard: Box::new(guard),
            then_expr: Box::new(left),
            else_expr: Box::new(right),
            position: Position::default(),
        })
    }

    pub fn unfolding(
        predicate: Type,
        args: Vec<Expr>,
        expr: Expr,
        perm: PermAmount,
        variant: MaybeEnumVariantIndex,
    ) -> Self {
        Expr::Unfolding(Unfolding {
            predicate,
            arguments: args,
            base: Box::new(expr),
            permission: perm,
            variant,
            position: Position::default(),
        })
    }

    pub fn unfolding_with_pos(
        predicate: Type,
        args: Vec<Expr>,
        expr: Expr,
        perm: PermAmount,
        variant: MaybeEnumVariantIndex,
        position: Position,
    ) -> Self {
        Expr::Unfolding(Unfolding {
            predicate,
            arguments: args,
            base: Box::new(expr),
            permission: perm,
            variant,
            position,
        })
    }

    /// Create `unfolding T(arg) in body` where `T` is the type of `arg`.
    pub fn wrap_in_unfolding(arg: Expr, body: Expr) -> Expr {
        let typ = arg.get_type();
        let pos = body.pos();
        Expr::Unfolding(Unfolding {
            predicate: typ.clone(),
            arguments: vec![arg],
            base: Box::new(body),
            permission: PermAmount::Read,
            variant: None,
            position: pos,
        })
    }

    pub fn func_app(
        name: String,
        type_arguments: Vec<Type>,
        args: Vec<Expr>,
        internal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Self {
        Expr::FuncApp(FuncApp {
            function_name: name,
            type_arguments,
            arguments: args,
            formal_arguments: internal_args,
            return_type,
            position: pos,
        })
    }

    pub fn domain_func_app(func: DomainFunc, args: Vec<Expr>) -> Self {
        Expr::DomainFuncApp(DomainFuncApp {
            domain_function: func,
            arguments: args,
            position: Position::default(),
        })
    }

    pub fn magic_wand(lhs: Expr, rhs: Expr, borrow: Option<Borrow>) -> Self {
        Expr::MagicWand(MagicWand {
            left: Box::new(lhs),
            right: Box::new(rhs),
            borrow,
            position: Position::default(),
        })
    }

    pub fn downcast(base: Expr, enum_place: Expr, variant_field: Field) -> Self {
        Expr::Downcast(DowncastExpr {
            base: Box::new(base),
            enum_place: Box::new(enum_place),
            field: variant_field,
        })
    }

    pub fn snap_app(expr: Expr) -> Self {
        Expr::SnapApp(SnapApp {
            base: Box::new(expr),
            position: Position::default(),
        })
    }

    pub fn find(&self, sub_target: &Expr) -> bool {
        pub struct ExprFinder<'a> {
            sub_target: &'a Expr,
            found: bool,
        }
        impl<'a> ExprWalker for ExprFinder<'a> {
            fn walk(&mut self, expr: &Expr) {
                if expr == self.sub_target {
                    self.found = true;
                } else {
                    default_walk_expr(self, expr)
                }
            }
        }

        let mut finder = ExprFinder {
            sub_target,
            found: false,
        };
        finder.walk(self);
        finder.found
    }

    /// Extract all predicates places mentioned in the expression whose predicates have the given
    /// permission amount.
    pub fn extract_predicate_places(&self, perm_amount: PermAmount) -> Vec<Expr> {
        pub struct PredicateFinder {
            predicates: Vec<Expr>,
            perm_amount: PermAmount,
        }
        impl ExprWalker for PredicateFinder {
            fn walk_predicate_access_predicate(
                &mut self,
                PredicateAccessPredicate {
                    box argument,
                    permission,
                    ..
                }: &PredicateAccessPredicate,
            ) {
                if *permission == self.perm_amount {
                    self.predicates.push(argument.clone());
                }
            }
        }

        let mut finder = PredicateFinder {
            predicates: Vec::new(),
            perm_amount,
        };
        finder.walk(self);
        finder.predicates
    }

    /// Split place into place components.
    pub fn explode_place(&self) -> (Expr, Vec<PlaceComponent>) {
        match self {
            Expr::Variant(Variant {
                base,
                variant_index,
                position,
            }) => {
                let (base_base, mut components) = base.explode_place();
                components.push(PlaceComponent::Variant(variant_index.clone(), *position));
                (base_base, components)
            }
            Expr::Field(FieldExpr {
                base,
                field,
                position,
            }) => {
                let (base_base, mut components) = base.explode_place();
                components.push(PlaceComponent::Field(field.clone(), *position));
                (base_base, components)
            }
            _ => (self.clone(), vec![]),
        }
    }

    /// Reconstruct place from the place components.
    #[must_use]
    pub fn reconstruct_place(self, components: Vec<PlaceComponent>) -> Expr {
        components
            .into_iter()
            .fold(self, |acc, component| match component {
                PlaceComponent::Variant(variant, pos) => Expr::Variant(Variant {
                    base: Box::new(acc),
                    variant_index: variant,
                    position: pos,
                }),
                PlaceComponent::Field(field, pos) => Expr::Field(FieldExpr {
                    base: Box::new(acc),
                    field,
                    position: pos,
                }),
            })
    }

    // Methods from the old `Place` structure

    pub fn local(local: LocalVar) -> Self {
        Expr::Local(Local {
            variable: local,
            position: Position::default(),
        })
    }

    pub fn local_with_pos(variable: LocalVar, position: Position) -> Self {
        Expr::Local(Local { variable, position })
    }

    #[must_use]
    pub fn variant(self, index: &str) -> Self {
        assert!(self.is_place());
        let field_name = format!("enum_{}", index);
        let typ = self.get_type();
        let variant = Field::new(field_name, typ.clone().variant(index));
        Expr::Variant(Variant {
            base: Box::new(self),
            variant_index: variant,
            position: Position::default(),
        })
    }

    #[must_use]
    pub fn field(self, field: Field) -> Self {
        Expr::Field(FieldExpr {
            base: Box::new(self),
            field,
            position: Position::default(),
        })
    }

    #[must_use]
    pub fn addr_of(self) -> Self {
        let addr_type = self.get_type().clone();
        Expr::AddrOf(AddrOf {
            base: Box::new(self),
            addr_type,
            position: Position::default(),
        })
    }

    pub fn is_only_permissions(&self) -> bool {
        match self {
            Expr::PredicateAccessPredicate(..) | Expr::FieldAccessPredicate(..) => true,
            Expr::BinOp(BinOp {
                op_kind: BinaryOpKind::And,
                left,
                right,
                ..
            }) => left.is_only_permissions() && right.is_only_permissions(),
            _ => false,
        }
    }

    pub fn is_place(&self) -> bool {
        match self {
            &Expr::Local(_) => true,
            &Expr::Variant(Variant { ref base, .. })
            | &Expr::Field(FieldExpr { ref base, .. })
            | &Expr::AddrOf(AddrOf { ref base, .. })
            | &Expr::LabelledOld(LabelledOld { ref base, .. })
            | &Expr::Unfolding(Unfolding { ref base, .. }) => base.is_place(),
            _ => false,
        }
    }

    pub fn is_variant(&self) -> bool {
        matches!(self, Expr::Variant(..))
    }

    pub fn is_call(&self) -> bool {
        matches!(self, Expr::FuncApp(..) | Expr::DomainFuncApp(..))
    }

    /// How many parts this place has? Used for ordering places.
    pub fn place_depth(&self) -> u32 {
        match self {
            &Expr::Local(_) => 1,
            &Expr::Variant(Variant { ref base, .. })
            | &Expr::Field(FieldExpr { ref base, .. })
            | &Expr::AddrOf(AddrOf { ref base, .. })
            | &Expr::LabelledOld(LabelledOld { ref base, .. })
            | &Expr::Unfolding(Unfolding { ref base, .. }) => base.place_depth() + 1,
            x => unreachable!("{:?}", x),
        }
    }

    pub fn is_simple_place(&self) -> bool {
        match self {
            &Expr::Local(_) => true,
            &Expr::Variant(Variant { ref base, .. }) | &Expr::Field(FieldExpr { ref base, .. }) => {
                base.is_simple_place()
            }
            _ => false,
        }
    }

    /// Only defined for places
    pub fn get_parent_ref(&self) -> Option<&Expr> {
        debug_assert!(self.is_place());
        match self {
            &Expr::Local(_) => None,
            &Expr::Variant(Variant { box ref base, .. })
            | &Expr::Field(FieldExpr { box ref base, .. })
            | &Expr::AddrOf(AddrOf { box ref base, .. }) => Some(base),
            &Expr::LabelledOld(_) => None,
            &Expr::Unfolding(_) => None,
            ref x => unreachable!("{}", x),
        }
    }

    /// Only defined for places
    pub fn get_parent(&self) -> Option<Expr> {
        self.get_parent_ref().cloned()
    }

    /// Is this place a MIR reference?
    pub fn is_mir_reference(&self) -> bool {
        debug_assert!(self.is_place());
        if let Expr::Field(FieldExpr {
            base:
                box Expr::Local(Local {
                    variable: LocalVar { typ, .. },
                    ..
                }),
            ..
        }) = self
        {
            return typ.is_mir_reference();
        }
        false
    }

    /// If self is a MIR reference, dereference it.
    pub fn try_deref(&self) -> Option<Self> {
        let typ = self.get_type();
        if typ.is_mir_reference() {
            if let Type::TypedRef(TypedRef { arguments, .. }) = self.get_type() {
                assert_eq!(arguments.len(), 1);
                let field_type = arguments[0].clone();
                let field = Field::new("val_ref", field_type);
                let field_place = self.clone().field(field);
                return Some(field_place);
            }
        }
        None
    }

    pub fn is_local(&self) -> bool {
        matches!(self, &Expr::Local(..))
    }

    pub fn is_addr_of(&self) -> bool {
        matches!(self, &Expr::AddrOf(..))
    }

    /// Puts an `old[label](..)` around the expression
    #[must_use]
    pub fn old<S: fmt::Display + ToString>(self, label: S) -> Self {
        match self {
            Expr::Local(..) => {
                /*
                debug!(
                    "Trying to put an old expression 'old[{}](..)' around {}, which is a local variable",
                    label,
                    self
                );
                */
                self
            }
            Expr::LabelledOld(..) => {
                /*
                debug!(
                    "Trying to put an old expression 'old[{}](..)' around {}, which already has a label",
                    label,
                    self
                );
                */
                self
            }
            _ => Expr::LabelledOld(LabelledOld {
                label: label.to_string(),
                base: Box::new(self),
                position: Position::default(),
            }),
        }
    }

    pub fn is_old(&self) -> bool {
        self.get_label().is_some()
    }

    pub fn is_curr(&self) -> bool {
        !self.is_old()
    }

    pub fn get_place(&self) -> Option<&Expr> {
        match self {
            Expr::PredicateAccessPredicate(PredicateAccessPredicate {
                argument: box arg, ..
            }) => Some(arg),
            Expr::FieldAccessPredicate(FieldAccessPredicate { base: box arg, .. }) => Some(arg),
            _ => None,
        }
    }

    pub fn get_perm_amount(&self) -> PermAmount {
        match self {
            Expr::PredicateAccessPredicate(PredicateAccessPredicate { permission, .. }) => {
                *permission
            }
            Expr::FieldAccessPredicate(FieldAccessPredicate { permission, .. }) => *permission,
            x => unreachable!("{}", x),
        }
    }

    pub fn is_pure(&self) -> bool {
        struct PurityFinder {
            non_pure: bool,
        }
        impl ExprWalker for PurityFinder {
            fn walk_predicate_access_predicate(
                &mut self,
                _predicate_access_predicate: &PredicateAccessPredicate,
            ) {
                self.non_pure = true;
            }
            fn walk_field_access_predicate(
                &mut self,
                _field_access_predicate: &FieldAccessPredicate,
            ) {
                self.non_pure = true;
            }
        }
        let mut walker = PurityFinder { non_pure: false };
        walker.walk(self);
        !walker.non_pure
    }

    /// Remove access predicates.
    #[must_use]
    pub fn purify(self) -> Self {
        struct Purifier;
        impl ExprFolder for Purifier {
            fn fold_predicate_access_predicate(
                &mut self,
                _predicate_access_predicate: PredicateAccessPredicate,
            ) -> Expr {
                true.into()
            }
            fn fold_field_access_predicate(
                &mut self,
                _field_access_predicate: FieldAccessPredicate,
            ) -> Expr {
                true.into()
            }
        }
        Purifier.fold(self)
    }

    pub fn is_heap_dependent(&self) -> bool {
        struct HeapAccessFinder {
            non_pure: bool,
        }
        impl ExprWalker for HeapAccessFinder {
            fn walk_predicate_access_predicate(
                &mut self,
                _predicate_access_predicate: &PredicateAccessPredicate,
            ) {
                self.non_pure = true;
            }
            fn walk_field_access_predicate(
                &mut self,
                _field_access_predicate: &FieldAccessPredicate,
            ) {
                self.non_pure = true;
            }
            fn walk_field(&mut self, _field: &FieldExpr) {
                self.non_pure = true;
            }
            fn walk_variant(&mut self, _variant: &Variant) {
                self.non_pure = true;
            }
            fn walk_magic_wand(&mut self, _magic_wand: &MagicWand) {
                self.non_pure = true;
            }
            fn walk_unfolding(&mut self, _unfolding: &Unfolding) {
                self.non_pure = true;
            }
            fn walk_func_app(&mut self, _func_app: &FuncApp) {
                self.non_pure = true;
            }
        }
        let mut walker = HeapAccessFinder { non_pure: false };
        walker.walk(self);
        walker.non_pure
    }

    /// Only defined for places
    pub fn get_base(&self) -> LocalVar {
        debug_assert!(self.is_place());
        match self {
            Expr::Local(Local { variable, .. }) => variable.clone(),
            Expr::LabelledOld(LabelledOld { base, .. })
            | Expr::Unfolding(Unfolding { base, .. }) => base.get_base(),
            _ => self.get_parent().unwrap().get_base(),
        }
    }

    pub fn get_label(&self) -> Option<&String> {
        match self {
            Expr::LabelledOld(LabelledOld { label, .. }) => Some(label),
            _ => None,
        }
    }

    pub fn has_proper_prefix(&self, other: &Expr) -> bool {
        debug_assert!(self.is_place(), "self={} other={}", self, other);
        debug_assert!(other.is_place(), "self={} other={}", self, other);
        self != other && self.has_prefix(other)
    }

    pub fn has_prefix(&self, other: &Expr) -> bool {
        debug_assert!(self.is_place());
        debug_assert!(other.is_place());
        if self == other {
            true
        } else {
            match self.get_parent() {
                Some(parent) => parent.has_prefix(other),
                None => false,
            }
        }
    }

    pub fn all_proper_prefixes(&self) -> Vec<Expr> {
        debug_assert!(self.is_place());
        match self.get_parent() {
            Some(parent) => parent.all_prefixes(),
            None => vec![],
        }
    }

    // Returns all prefixes, from the shortest to the longest
    pub fn all_prefixes(&self) -> Vec<Expr> {
        debug_assert!(self.is_place());
        let mut res = self.all_proper_prefixes();
        res.push(self.clone());
        res
    }

    /// Returns the type of the expression.
    /// For function applications, the return type is provided.
    pub fn get_type(&self) -> &Type {
        lazy_static::lazy_static! {
            static ref FN_PTR_TYPE: Type = Type::typed_ref("FnPtr");
        }
        match self {
            Expr::Local(Local {
                variable: LocalVar { typ, .. },
                ..
            })
            | Expr::Variant(Variant {
                variant_index: Field { typ, .. },
                ..
            })
            | Expr::Field(FieldExpr {
                field: Field { typ, .. },
                ..
            })
            | Expr::AddrOf(AddrOf { addr_type: typ, .. })
            | Expr::LetExpr(LetExpr {
                variable: LocalVar { typ, .. },
                ..
            }) => typ,
            Expr::LabelledOld(LabelledOld { base, .. })
            | Expr::Unfolding(Unfolding { base, .. })
            | Expr::UnaryOp(UnaryOp { argument: base, .. }) => base.get_type(),
            Expr::FuncApp(FuncApp { return_type, .. }) => return_type,
            Expr::DomainFuncApp(DomainFuncApp {
                domain_function, ..
            }) => &domain_function.return_type,
            Expr::Const(ConstExpr { value, .. }) => match value {
                Const::Bool(..) => &Type::Bool,
                Const::Int(..) | Const::BigInt(..) => &Type::Int,
                Const::Float(FloatConst::F32(..)) => &Type::Float(Float::F32),
                Const::Float(FloatConst::F64(..)) => &Type::Float(Float::F64),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Signed(BitVectorSize::BV8),
                    ..
                }) => &Type::BitVector(BitVector::Signed(BitVectorSize::BV8)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Signed(BitVectorSize::BV16),
                    ..
                }) => &Type::BitVector(BitVector::Signed(BitVectorSize::BV16)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Signed(BitVectorSize::BV32),
                    ..
                }) => &Type::BitVector(BitVector::Signed(BitVectorSize::BV32)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Signed(BitVectorSize::BV64),
                    ..
                }) => &Type::BitVector(BitVector::Signed(BitVectorSize::BV64)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Signed(BitVectorSize::BV128),
                    ..
                }) => &Type::BitVector(BitVector::Signed(BitVectorSize::BV128)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Unsigned(BitVectorSize::BV8),
                    ..
                }) => &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV8)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Unsigned(BitVectorSize::BV16),
                    ..
                }) => &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV16)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Unsigned(BitVectorSize::BV32),
                    ..
                }) => &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV32)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Unsigned(BitVectorSize::BV64),
                    ..
                }) => &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV64)),
                Const::BitVector(BitVectorConst {
                    typ: BitVector::Unsigned(BitVectorSize::BV128),
                    ..
                }) => &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV128)),
                Const::FnPtr => &FN_PTR_TYPE,
            },
            Expr::BinOp(BinOp {
                op_kind,
                left,
                right,
                ..
            }) => match op_kind {
                BinaryOpKind::EqCmp
                | BinaryOpKind::NeCmp
                | BinaryOpKind::GtCmp
                | BinaryOpKind::GeCmp
                | BinaryOpKind::LtCmp
                | BinaryOpKind::LeCmp
                | BinaryOpKind::And
                | BinaryOpKind::Or
                | BinaryOpKind::Implies => &Type::Bool,
                BinaryOpKind::Add
                | BinaryOpKind::Sub
                | BinaryOpKind::Mul
                | BinaryOpKind::Div
                | BinaryOpKind::Mod
                | BinaryOpKind::BitAnd
                | BinaryOpKind::BitOr
                | BinaryOpKind::BitXor
                | BinaryOpKind::Shl
                | BinaryOpKind::LShr
                | BinaryOpKind::AShr
                | BinaryOpKind::Min
                | BinaryOpKind::Max => {
                    let typ1 = left.get_type();
                    let typ2 = right.get_type();
                    assert_eq!(typ1, typ2, "expr: {:?}", self);
                    typ1
                }
            },
            Expr::Cond(Cond {
                then_expr,
                else_expr,
                ..
            }) => {
                let typ1 = then_expr.get_type();
                let typ2 = else_expr.get_type();
                assert_eq!(typ1, typ2, "expr: {:?}", self);
                typ1
            }
            Expr::ForAll(..) | Expr::Exists(..) => &Type::Bool,
            Expr::MagicWand(..)
            | Expr::PredicateAccessPredicate(..)
            | Expr::FieldAccessPredicate(..)
            | Expr::InhaleExhale(..) => {
                unreachable!("Unexpected expression: {:?}", self);
            }
            Expr::Downcast(DowncastExpr { base, .. }) => base.get_type(),
            // Note: SnapApp returns the same type as the wrapped expression,
            // to allow for e.g. field access without special considerations.
            // SnapApps are replaced later in the encoder.
            Expr::SnapApp(SnapApp { base, .. }) => base.get_type(),
            Expr::ContainerOp(ContainerOp {
                op_kind,
                left,
                right,
                ..
            }) => {
                todo!("get_type container_op({:?}, {}, {})", op_kind, left, right)
            }
            Expr::Map(Map { typ, .. }) | Expr::Seq(Seq { typ, .. }) => typ,
            Expr::Cast(Cast { kind, .. }) => match kind {
                CastKind::BVIntoInt(_) => &Type::Int,
                CastKind::IntIntoBV(BitVector::Signed(BitVectorSize::BV8)) => {
                    &Type::BitVector(BitVector::Signed(BitVectorSize::BV8))
                }
                CastKind::IntIntoBV(BitVector::Signed(BitVectorSize::BV16)) => {
                    &Type::BitVector(BitVector::Signed(BitVectorSize::BV16))
                }
                CastKind::IntIntoBV(BitVector::Signed(BitVectorSize::BV32)) => {
                    &Type::BitVector(BitVector::Signed(BitVectorSize::BV32))
                }
                CastKind::IntIntoBV(BitVector::Signed(BitVectorSize::BV64)) => {
                    &Type::BitVector(BitVector::Signed(BitVectorSize::BV64))
                }
                CastKind::IntIntoBV(BitVector::Signed(BitVectorSize::BV128)) => {
                    &Type::BitVector(BitVector::Signed(BitVectorSize::BV128))
                }
                CastKind::IntIntoBV(BitVector::Unsigned(BitVectorSize::BV8)) => {
                    &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV8))
                }
                CastKind::IntIntoBV(BitVector::Unsigned(BitVectorSize::BV16)) => {
                    &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV16))
                }
                CastKind::IntIntoBV(BitVector::Unsigned(BitVectorSize::BV32)) => {
                    &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV32))
                }
                CastKind::IntIntoBV(BitVector::Unsigned(BitVectorSize::BV64)) => {
                    &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV64))
                }
                CastKind::IntIntoBV(BitVector::Unsigned(BitVectorSize::BV128)) => {
                    &Type::BitVector(BitVector::Unsigned(BitVectorSize::BV128))
                }
            },
        }
    }

    /// If returns true, then the expression is guaranteed to be boolean. However, it may return
    /// false even for boolean expressions.
    pub fn is_bool(&self) -> bool {
        if self.is_place() {
            self.get_type() == &Type::Bool
        } else {
            match self {
                Expr::Const(ConstExpr {
                    value: Const::Bool(_),
                    ..
                })
                | Expr::UnaryOp(UnaryOp {
                    op_kind: UnaryOpKind::Not,
                    ..
                })
                | Expr::FuncApp(FuncApp {
                    return_type: Type::Bool,
                    ..
                })
                | Expr::ForAll(..)
                | Expr::Exists(..) => true,
                Expr::BinOp(BinOp { op_kind, .. }) => {
                    use self::BinaryOpKind::*;
                    *op_kind == EqCmp
                        || *op_kind == NeCmp
                        || *op_kind == GtCmp
                        || *op_kind == GeCmp
                        || *op_kind == LtCmp
                        || *op_kind == LeCmp
                        || *op_kind == And
                        || *op_kind == Or
                        || *op_kind == Implies
                }
                _ => false,
            }
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.get_type() {
            t @ &Type::TypedRef(..) | t @ &Type::TypeVar(_) => Some(t.name()),
            _ => None,
        }
    }

    #[must_use]
    pub fn negate(self) -> Self {
        if let Expr::UnaryOp(UnaryOp {
            op_kind: UnaryOpKind::Not,
            box argument,
            ..
        }) = self
        {
            argument
        } else {
            Expr::not(self)
        }
    }

    #[must_use]
    pub fn map_labels<F>(self, f: F) -> Self
    where
        F: Fn(String) -> Option<String>,
    {
        struct OldLabelReplacer<T: Fn(String) -> Option<String>> {
            f: T,
        }
        impl<T: Fn(String) -> Option<String>> ExprFolder for OldLabelReplacer<T> {
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> Expr {
                match (self.f)(label) {
                    Some(new_label) => base.old(new_label).set_pos(position),
                    None => *base,
                }
            }
        }
        OldLabelReplacer { f }.fold(self)
    }

    /// Simplify `Deref(AddrOf(P))` to `P`.
    #[must_use]
    pub fn simplify_addr_of(self) -> Self {
        struct Simplifier;
        impl ExprFolder for Simplifier {
            fn fold_field(
                &mut self,
                FieldExpr {
                    base: receiver,
                    field,
                    position,
                }: FieldExpr,
            ) -> Expr {
                if receiver.is_addr_of() {
                    if let Expr::AddrOf(AddrOf { base, .. }) = *receiver {
                        *base
                    } else {
                        unreachable!();
                    }
                } else {
                    let new_receiver = self.fold_boxed(receiver);
                    Expr::Field(FieldExpr {
                        base: new_receiver,
                        field,
                        position,
                    })
                }
            }
        }
        Simplifier.fold(self)
    }

    // TODO polymorphic: convert following 2 functions after type substitution is updated
    #[must_use]
    pub fn replace_place(self, target: &Expr, replacement: &Expr) -> Self {
        // TODO: disabled for snapshot patching
        /*
        debug_assert!(target.is_place());
        assert_eq!(target.get_type(), replacement.get_type());
        if replacement.is_place() {
            assert!(
                // for copy types references are replaced by snapshots
                target.get_type() == replacement.get_type()
                    || replacement.get_type().is_snapshot(),
                "Cannot substitute '{}' with '{}', because they have incompatible types '{}' and '{}'",
                target,
                replacement,
                target.get_type(),
                replacement.get_type()
            );
        }
        */

        struct PlaceReplacer<'a> {
            target: &'a Expr,
            replacement: &'a Expr,
            subst: bool,
        }
        impl<'a> ExprFolder for PlaceReplacer<'a> {
            fn fold(&mut self, e: Expr) -> Expr {
                if e.is_place() && &e == self.target {
                    self.subst = true;
                    self.replacement.clone()
                } else {
                    let default_expr = default_fold_expr(self, e);
                    match default_expr {
                        Expr::Field(_) => default_expr,
                        x => {
                            self.subst = false;
                            x
                        }
                    }
                }
            }

            fn fold_forall(
                &mut self,
                ForAll {
                    variables,
                    triggers,
                    body,
                    position,
                }: ForAll,
            ) -> Expr {
                if variables.contains(&self.target.get_base()) {
                    // Do nothing
                    Expr::ForAll(ForAll {
                        variables,
                        triggers,
                        body,
                        position,
                    })
                } else {
                    Expr::ForAll(ForAll {
                        variables,
                        triggers: triggers
                            .into_iter()
                            .map(|x| x.replace_place(self.target, self.replacement))
                            .collect(),
                        body: self.fold_boxed(body),
                        position,
                    })
                }
            }

            fn fold_exists(
                &mut self,
                Exists {
                    variables,
                    triggers,
                    body,
                    position,
                }: Exists,
            ) -> Expr {
                if variables.contains(&self.target.get_base()) {
                    // Do nothing
                    Expr::Exists(Exists {
                        variables,
                        triggers,
                        body,
                        position,
                    })
                } else {
                    Expr::Exists(Exists {
                        variables,
                        triggers: triggers
                            .into_iter()
                            .map(|x| x.replace_place(self.target, self.replacement))
                            .collect(),
                        body: self.fold_boxed(body),
                        position,
                    })
                }
            }
        }
        PlaceReplacer {
            target,
            replacement,
            subst: false,
        }
        .fold(self)
    }

    #[must_use]
    pub fn replace_multiple_places(self, replacements: &[(Expr, Expr)]) -> Self {
        // TODO: disabled for snapshot patching
        /*
        for (src, dst) in replacements {
            debug_assert!(src.is_place() && dst.is_place());
            if dst.is_place() {
                assert!(
                    // for copy types references are replaced by snapshots
                    src.get_type() == dst.get_type() || dst.get_type().is_snapshot(),
                    "Cannot substitute '{}' with '{}', because they have incompatible \
                    types '{}' and '{}'",
                    src,
                    dst,
                    src.get_type(),
                    dst.get_type()
                );
            }
        }
        */

        struct PlaceReplacer<'a> {
            replacements: &'a [(Expr, Expr)],
        }
        impl<'a> ExprFolder for PlaceReplacer<'a> {
            fn fold(&mut self, e: Expr) -> Expr {
                // Check if this matches a substitution.
                if e.is_place() {
                    let substitution = self.replacements.iter().find(|(src, _)| src == &e);
                    if let Some((_src, dst)) = substitution {
                        return dst.clone();
                    }
                }

                // Otherwise, keep folding
                default_fold_expr(self, e)
            }

            fn fold_field(
                &mut self,
                FieldExpr {
                    mut base,
                    field,
                    position,
                }: FieldExpr,
            ) -> Expr {
                base = self.fold_boxed(base);

                Expr::Field(FieldExpr {
                    base,
                    field,
                    position,
                })
            }

            fn fold_forall(
                &mut self,
                ForAll {
                    variables,
                    triggers,
                    body,
                    position,
                }: ForAll,
            ) -> Expr {
                // TODO: the correct solution is the following:
                // (1) skip replacements where `src` uses a quantified variable;
                // (2) rename with a fresh name the quantified variables that conflict with `dst`.
                for (src, dst) in self.replacements.iter() {
                    if variables.contains(&src.get_base()) || variables.contains(&dst.get_base()) {
                        unimplemented!(
                            "replace_multiple_places doesn't handle replacements that conflict \
                            with quantified variables"
                        )
                    }
                }

                Expr::ForAll(ForAll {
                    variables,
                    triggers: triggers
                        .into_iter()
                        .map(|x| x.replace_multiple_places(self.replacements))
                        .collect(),
                    body: self.fold_boxed(body),
                    position,
                })
            }

            fn fold_exists(
                &mut self,
                Exists {
                    variables,
                    triggers,
                    body,
                    position,
                }: Exists,
            ) -> Expr {
                // TODO: the correct solution is the following:
                // (1) skip replacements where `src` uses a quantified variable;
                // (2) rename with a fresh name the quantified variables that conflict with `dst`.
                for (src, dst) in self.replacements.iter() {
                    if variables.contains(&src.get_base()) || variables.contains(&dst.get_base()) {
                        unimplemented!(
                            "replace_multiple_places doesn't handle replacements that conflict \
                            with quantified variables"
                        )
                    }
                }

                Expr::Exists(Exists {
                    variables,
                    triggers: triggers
                        .into_iter()
                        .map(|x| x.replace_multiple_places(self.replacements))
                        .collect(),
                    body: self.fold_boxed(body),
                    position,
                })
            }
        }
        PlaceReplacer { replacements }.fold(self)
    }

    /// Replaces expressions like `old[l5](old[l5](_9.val_ref).foo.bar)`
    /// into `old[l5](_9.val_ref.foo.bar)`
    #[must_use]
    pub fn remove_redundant_old(self) -> Self {
        struct RedundantOldRemover {
            current_label: Option<String>,
        }
        impl ExprFolder for RedundantOldRemover {
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> Expr {
                let old_current_label = mem::replace(&mut self.current_label, Some(label.clone()));
                let new_base = default_fold_expr(self, *base);
                let new_expr = if Some(label.clone()) == old_current_label {
                    new_base
                } else {
                    new_base.old(label).set_pos(position)
                };
                self.current_label = old_current_label;
                new_expr
            }
        }
        RedundantOldRemover {
            current_label: None,
        }
        .fold(self)
    }

    /// Leaves a conjunction of `acc(..)` expressions
    #[must_use]
    pub fn filter_perm_conjunction(self) -> Self {
        struct PermConjunctionFilter();
        impl ExprFolder for PermConjunctionFilter {
            fn fold(&mut self, e: Expr) -> Expr {
                match e {
                    f @ Expr::PredicateAccessPredicate(..) => f,
                    f @ Expr::FieldAccessPredicate(..) => f,
                    Expr::BinOp(BinOp {
                        op_kind: BinaryOpKind::And,
                        left,
                        right,
                        position,
                    }) => self.fold_bin_op(BinOp {
                        op_kind: BinaryOpKind::And,
                        left,
                        right,
                        position,
                    }),

                    Expr::BinOp(..)
                    | Expr::MagicWand(..)
                    | Expr::Unfolding(..)
                    | Expr::Cond(..)
                    | Expr::UnaryOp(..)
                    | Expr::Const(..)
                    | Expr::Local(..)
                    | Expr::Variant(..)
                    | Expr::Field(..)
                    | Expr::AddrOf(..)
                    | Expr::LabelledOld(..)
                    | Expr::ForAll(..)
                    | Expr::Exists(..)
                    | Expr::LetExpr(..)
                    | Expr::FuncApp(..)
                    | Expr::DomainFuncApp(..)
                    | Expr::InhaleExhale(..)
                    | Expr::Downcast(..)
                    | Expr::ContainerOp(..)
                    | Expr::Seq(..)
                    | Expr::Map(..)
                    | Expr::SnapApp(..)
                    | Expr::Cast(..) => true.into(),
                }
            }
        }
        PermConjunctionFilter().fold(self)
    }

    pub fn local_type(&self) -> String {
        match &self {
            Expr::Local(Local { variable, .. }) => match &variable.typ {
                t @ Type::TypedRef(..) => t.name(),
                _ => panic!("expected Type::TypedRef"),
            },
            _ => panic!("expected Expr::Local"),
        }
    }

    /// Compute the permissions that are needed for this expression to
    /// be successfully evaluated. This is method is used for `fold` and
    /// `exhale` statements inside `package` statements because Silicon
    /// fails to compute which permissions it should take into the magic
    /// wand.
    pub fn compute_footprint(&self, perm_amount: PermAmount) -> Vec<Expr> {
        struct Collector {
            perm_amount: PermAmount,
            perms: Vec<Expr>,
        }
        impl ExprWalker for Collector {
            fn walk_variant(
                &mut self,
                Variant {
                    box base,
                    variant_index,
                    position,
                }: &Variant,
            ) {
                self.walk(base);
                let expr = Expr::Variant(Variant {
                    base: Box::new(base.clone()),
                    variant_index: variant_index.clone(),
                    position: *position,
                });
                let perm = Expr::acc_permission(expr, self.perm_amount);
                self.perms.push(perm);
            }
            fn walk_field(
                &mut self,
                FieldExpr {
                    box base,
                    field,
                    position,
                }: &FieldExpr,
            ) {
                self.walk(base);
                let expr = Expr::Field(FieldExpr {
                    base: Box::new(base.clone()),
                    field: field.clone(),
                    position: *position,
                });
                let perm = Expr::acc_permission(expr, self.perm_amount);
                self.perms.push(perm);
            }
            fn walk_labelled_old(&mut self, _labelled_old: &LabelledOld) {
                // Stop recursion.
            }
        }
        let mut collector = Collector {
            perm_amount,
            perms: Vec::new(),
        };
        collector.walk(self);
        collector.perms
    }

    // TODO: update this after type substitution is in place
    // /// Replace all generic types with their instantiations by using string substitution.
    // /// FIXME: this is a hack to support generics. See issue #187.
    #[must_use]
    pub fn patch_types(self, substs: &FxHashMap<TypeVar, Type>) -> Self {
        struct TypePatcher<'a> {
            substs: &'a FxHashMap<TypeVar, Type>,
        }
        impl<'a> ExprFolder for TypePatcher<'a> {
            fn fold_predicate_access_predicate(
                &mut self,
                PredicateAccessPredicate {
                    predicate_type,
                    argument,
                    permission,
                    position,
                }: PredicateAccessPredicate,
            ) -> Expr {
                Expr::PredicateAccessPredicate(PredicateAccessPredicate {
                    predicate_type: predicate_type.substitute(self.substs),
                    argument: self.fold_boxed(argument),
                    permission,
                    position,
                })
            }
            fn fold_local(
                &mut self,
                Local {
                    mut variable,
                    position,
                }: Local,
            ) -> Expr {
                variable.typ = variable.typ.substitute(self.substs);
                Expr::Local(Local { variable, position })
            }
            fn fold_field(
                &mut self,
                FieldExpr {
                    base,
                    field,
                    position,
                }: FieldExpr,
            ) -> Expr {
                Expr::Field(FieldExpr {
                    base: self.fold_boxed(base),
                    field: Field {
                        name: field.name,
                        typ: field.typ.substitute(self.substs),
                    },
                    position,
                })
            }
            fn fold_func_app(
                &mut self,
                FuncApp {
                    function_name,
                    type_arguments,
                    arguments,
                    formal_arguments,
                    return_type,
                    position,
                }: FuncApp,
            ) -> Expr {
                let formal_arguments = formal_arguments
                    .into_iter()
                    .map(|mut var| {
                        var.typ = var.typ.substitute(self.substs);
                        var
                    })
                    .collect();
                // FIXME: We do not patch the return_type because pure functions cannot return
                // generic values.
                Expr::FuncApp(FuncApp {
                    function_name,
                    type_arguments,
                    arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
                    formal_arguments,
                    return_type,
                    position,
                })
            }
        }
        let mut patcher = TypePatcher { substs };
        patcher.fold(self)
    }

    /// Is this expression a constant?
    pub fn is_constant(&self) -> bool {
        match self {
            Expr::Const(_) => true,
            Expr::UnaryOp(UnaryOp { argument, .. }) => argument.is_constant(),
            Expr::BinOp(BinOp { left, right, .. }) => left.is_constant() && right.is_constant(),
            _ => false,
        }
    }

    /// Remove read permissions. For example, if the expression is
    /// `acc(x.f, read) && acc(P(x.f), write)`, then after the
    /// transformation it will be: `acc(P(x.f), write)`.
    #[must_use]
    pub fn remove_read_permissions(self) -> Self {
        struct ReadPermRemover {}
        impl ExprFolder for ReadPermRemover {
            fn fold_predicate_access_predicate(
                &mut self,
                PredicateAccessPredicate {
                    predicate_type,
                    argument,
                    permission,
                    position,
                }: PredicateAccessPredicate,
            ) -> Expr {
                assert!(permission.is_valid_for_specs());
                match permission {
                    PermAmount::Write => Expr::PredicateAccessPredicate(PredicateAccessPredicate {
                        predicate_type,
                        argument,
                        permission,
                        position,
                    }),
                    PermAmount::Read => true.into(),
                    _ => unreachable!(),
                }
            }
            fn fold_field_access_predicate(
                &mut self,
                FieldAccessPredicate {
                    base,
                    permission,
                    position,
                }: FieldAccessPredicate,
            ) -> Expr {
                assert!(permission.is_valid_for_specs());
                match permission {
                    PermAmount::Write => Expr::FieldAccessPredicate(FieldAccessPredicate {
                        base,
                        permission,
                        position,
                    }),
                    PermAmount::Read => true.into(),
                    _ => unreachable!(),
                }
            }
        }
        let mut remover = ReadPermRemover {};
        remover.fold(self)
    }
}

/// A component that can be used to represent a place as a vector.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceComponent {
    Field(Field, Position),
    Variant(Field, Position),
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub enum UnaryOpKind {
    Not,
    Minus,
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub enum BinaryOpKind {
    EqCmp,
    NeCmp,
    GtCmp,
    GeCmp,
    LtCmp,
    LeCmp,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Implies,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    LShr,
    AShr,
    Min,
    Max,
}

#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub enum ContainerOpKind {
    SeqIndex,
    SeqConcat,
    SeqLen,
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub enum FloatConst {
    F32(u32),
    F64(u64),
}

impl fmt::Display for FloatConst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub struct BitVectorConst {
    pub value: String,
    pub typ: BitVector,
}

impl fmt::Display for BitVectorConst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({})", self.typ, self.value)
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize, PartialOrd, Ord,
)]
pub enum Const {
    Bool(bool),
    Int(i64),
    BigInt(String),
    Float(FloatConst),
    BitVector(BitVectorConst),
    /// All function pointers share the same constant, because their function
    /// is determined by the type system.
    FnPtr,
}

/// Individual structs for different cases of Expr
#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Local {
    pub variable: LocalVar,
    pub position: Position,
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.variable)
    }
}

impl PartialEq for Local {
    fn eq(&self, other: &Self) -> bool {
        self.variable == other.variable
    }
}

impl Hash for Local {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.variable).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Variant {
    pub base: Box<Expr>,
    pub variant_index: Field,
    pub position: Position,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}[{}]", &self.base, &self.variant_index)
    }
}

impl PartialEq for Variant {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.variant_index) == (&*other.base, &other.variant_index)
    }
}

impl Hash for Variant {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, &self.variant_index).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct FieldExpr {
    pub base: Box<Expr>,
    pub field: Field,
    pub position: Position,
}

impl fmt::Display for FieldExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", &self.base, &self.field)
    }
}

impl PartialEq for FieldExpr {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.field) == (&*other.base, &other.field)
    }
}

impl Hash for FieldExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, &self.field).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct AddrOf {
    pub base: Box<Expr>,
    pub addr_type: Type,
    pub position: Position,
}

impl fmt::Display for AddrOf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "&({})", &self.base)
    }
}

impl PartialEq for AddrOf {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &self.addr_type) == (&*other.base, &other.addr_type)
    }
}

impl Hash for AddrOf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, &self.addr_type).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct LabelledOld {
    pub label: String,
    pub base: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for LabelledOld {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "old[{}]({})", &self.label, &self.base)
    }
}

impl PartialEq for LabelledOld {
    fn eq(&self, other: &Self) -> bool {
        (&self.label, &*self.base) == (&other.label, &*other.base)
    }
}

impl Hash for LabelledOld {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.label, &*self.base).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct ConstExpr {
    pub value: Const,
    pub position: Position,
}

impl fmt::Display for ConstExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}

impl PartialEq for ConstExpr {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Hash for ConstExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.value).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct MagicWand {
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub borrow: Option<Borrow>,
    pub position: Position,
}

impl fmt::Display for MagicWand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({}) {:?} --* ({})",
            &self.left, &self.borrow, &self.right
        )
    }
}

impl PartialEq for MagicWand {
    fn eq(&self, other: &Self) -> bool {
        (&*self.left, &*self.right, self.borrow) == (&*other.left, &*other.right, other.borrow)
    }
}

impl Hash for MagicWand {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.left, &*self.right, self.borrow).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct PredicateAccessPredicate {
    pub predicate_type: Type,
    pub argument: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

impl fmt::Display for PredicateAccessPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "acc({}({}), {})",
            &self.predicate_type.encode_as_string(),
            &self.argument,
            self.permission
        )
    }
}

impl PartialEq for PredicateAccessPredicate {
    fn eq(&self, other: &Self) -> bool {
        (&self.predicate_type, &self.argument, self.permission)
            == (&other.predicate_type, &other.argument, other.permission)
    }
}

impl Hash for PredicateAccessPredicate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.predicate_type, &self.argument, self.permission).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct FieldAccessPredicate {
    pub base: Box<Expr>,
    pub permission: PermAmount,
    pub position: Position,
}

impl fmt::Display for FieldAccessPredicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "acc({}, {})", &self.base, self.permission)
    }
}

impl PartialEq for FieldAccessPredicate {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, self.permission) == (&*other.base, other.permission)
    }
}

impl Hash for FieldAccessPredicate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, self.permission).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct UnaryOp {
    pub op_kind: UnaryOpKind,
    pub argument: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({})", &self.op_kind, &self.argument)
    }
}

impl PartialEq for UnaryOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.argument) == (&other.op_kind, &*other.argument)
    }
}

impl Hash for UnaryOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.op_kind, &*self.argument).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct BinOp {
    pub op_kind: BinaryOpKind,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}) {} ({})", &self.left, &self.op_kind, &self.right)
    }
}

impl PartialEq for BinOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.left, &*self.right) == (&other.op_kind, &*other.left, &*other.right)
    }
}

impl Hash for BinOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.op_kind, &*self.left, &*self.right).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct ContainerOp {
    pub op_kind: ContainerOpKind,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for ContainerOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.op_kind {
            ContainerOpKind::SeqIndex => write!(f, "{}[{}]", &self.left, &self.right),
            ContainerOpKind::SeqConcat => write!(f, "{} ++ {}", &self.left, &self.right),
            ContainerOpKind::SeqLen => write!(f, "|{}|", &self.left),
        }
    }
}

impl PartialEq for ContainerOp {
    fn eq(&self, other: &Self) -> bool {
        (&self.op_kind, &*self.left, &*self.right) == (&other.op_kind, &*other.left, &*other.right)
    }
}

impl Hash for ContainerOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.op_kind, &*self.left, &*self.right).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Seq {
    pub typ: Type,
    pub elements: Vec<Expr>,
    pub position: Position,
}

impl fmt::Display for Seq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let typ = &self.typ;
        let elems_printed = self
            .elements
            .iter()
            .map(|e| format!("{}", e))
            .collect::<Vec<_>>()
            .join(", ");
        let elem_ty = if let Type::Seq(seq_type) = typ {
            &*seq_type.typ
        } else {
            unreachable!()
        };
        write!(f, "Seq[{}]({})", elem_ty, elems_printed)
    }
}

impl PartialEq for Seq {
    fn eq(&self, other: &Self) -> bool {
        (&self.typ, &*self.elements) == (&other.typ, &*other.elements)
    }
}

impl Hash for Seq {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.typ, &*self.elements).hash(state);
    }
}

/// Corresponding to `ExplicitMap`, the elements are expressions of Maplets, i.e. key-value pairs
#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Map {
    /// *Map* type, not the type of keys or values
    pub typ: Type,
    /// a list of Maplets this map consists of
    pub elements: Vec<Expr>,
    pub position: Position,
}

impl PartialEq for Map {
    fn eq(&self, other: &Self) -> bool {
        (&self.typ, &*self.elements) == (&other.typ, &*other.elements)
    }
}

impl Hash for Map {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.typ, &*self.elements).hash(state);
    }
}

impl fmt::Display for Map {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let typ = &self.typ;
        let elems_printed = self
            .elements
            .iter()
            .map(|e| format!("{}", e))
            .collect::<Vec<_>>()
            .join(", ");
        let map_ty = match typ {
            Type::Map(m) => m,
            _ => unreachable!(),
        };
        write!(
            f,
            "Map[{}, {}]({})",
            map_ty.key_type, map_ty.val_type, elems_printed
        )
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Unfolding {
    pub predicate: Type,
    pub arguments: Vec<Expr>,
    pub base: Box<Expr>,
    pub permission: PermAmount,
    pub variant: MaybeEnumVariantIndex,
    pub position: Position,
}

impl fmt::Display for Unfolding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(unfolding acc({}({}), {}) in {})",
            if let Some(variant_index) = &self.variant {
                format!("{}<variant {}>", &self.predicate, variant_index)
            } else {
                (self.predicate).to_string()
            },
            &(self.arguments)
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.permission,
            &self.base
        )
    }
}

impl PartialEq for Unfolding {
    fn eq(&self, other: &Self) -> bool {
        (
            &self.predicate,
            &self.arguments,
            &*self.base,
            self.permission,
            &self.variant,
        ) == (
            &other.predicate,
            &other.arguments,
            &*other.base,
            other.permission,
            &other.variant,
        )
    }
}

impl Hash for Unfolding {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (
            &self.predicate,
            &self.arguments,
            &*self.base,
            self.permission,
            &self.variant,
        )
            .hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Cond {
    pub guard: Box<Expr>,
    pub then_expr: Box<Expr>,
    pub else_expr: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({})?({}):({})",
            &self.guard, &self.then_expr, &self.else_expr
        )
    }
}

impl PartialEq for Cond {
    fn eq(&self, other: &Self) -> bool {
        (&*self.guard, &*self.then_expr, &*self.else_expr)
            == (&*other.guard, &*other.then_expr, &*other.else_expr)
    }
}

impl Hash for Cond {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.guard, &*self.then_expr, &*self.else_expr).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct ForAll {
    pub variables: Vec<LocalVar>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for ForAll {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "forall {} {} :: {}",
            (self.variables)
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<String>>()
                .join(", "),
            (self.triggers)
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.body
        )
    }
}

impl PartialEq for ForAll {
    fn eq(&self, other: &Self) -> bool {
        (&self.variables, &self.triggers, &*self.body)
            == (&other.variables, &other.triggers, &*other.body)
    }
}

impl Hash for ForAll {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.variables, &self.triggers, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Exists {
    pub variables: Vec<LocalVar>,
    pub triggers: Vec<Trigger>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for Exists {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "exists {} {} :: {}",
            (self.variables)
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<String>>()
                .join(", "),
            (self.triggers)
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.body
        )
    }
}

impl PartialEq for Exists {
    fn eq(&self, other: &Self) -> bool {
        (&self.variables, &self.triggers, &*self.body)
            == (&other.variables, &other.triggers, &*other.body)
    }
}

impl Hash for Exists {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.variables, &self.triggers, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct LetExpr {
    pub variable: LocalVar,
    pub def: Box<Expr>,
    pub body: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for LetExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(let {:?} == ({}) in {})",
            &self.variable, self.def, self.body
        )
    }
}

impl PartialEq for LetExpr {
    fn eq(&self, other: &Self) -> bool {
        (&self.variable, &*self.def, &*self.body) == (&other.variable, &*other.def, &*other.body)
    }
}

impl Hash for LetExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.variable, &*self.def, &*self.body).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct FuncApp {
    pub function_name: String,
    pub type_arguments: Vec<Type>,
    pub arguments: Vec<Expr>,
    pub formal_arguments: Vec<LocalVar>,
    pub return_type: Type,
    pub position: Position,
}

impl fmt::Display for FuncApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}<{}>({})",
            &self.function_name,
            display::cjoin(&self.type_arguments),
            display::cjoin(&self.arguments),
        )
    }
}

impl PartialEq for FuncApp {
    fn eq(&self, other: &Self) -> bool {
        (&self.function_name, &self.type_arguments, &self.arguments)
            == (
                &other.function_name,
                &other.type_arguments,
                &other.arguments,
            )
    }
}

impl Hash for FuncApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.function_name, &self.type_arguments, &self.arguments).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct DomainFuncApp {
    pub domain_function: DomainFunc,
    pub arguments: Vec<Expr>,
    pub position: Position,
}

impl fmt::Display for DomainFuncApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}<{}>({})",
            self.domain_function.name,
            display::cjoin(&self.domain_function.type_arguments),
            display::cjoin(&self.arguments),
        )
    }
}

impl PartialEq for DomainFuncApp {
    fn eq(&self, other: &Self) -> bool {
        (&self.domain_function, &self.arguments) == (&other.domain_function, &other.arguments)
    }
}

impl Hash for DomainFuncApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.domain_function, &self.arguments).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct InhaleExhale {
    pub inhale_expr: Box<Expr>,
    pub exhale_expr: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for InhaleExhale {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[({}), ({})]", &self.inhale_expr, &self.exhale_expr)
    }
}

impl PartialEq for InhaleExhale {
    fn eq(&self, other: &Self) -> bool {
        (&*self.inhale_expr, &*self.exhale_expr) == (&*other.inhale_expr, &*other.exhale_expr)
    }
}

impl Hash for InhaleExhale {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.inhale_expr, &*self.exhale_expr).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct DowncastExpr {
    pub base: Box<Expr>,
    pub enum_place: Box<Expr>,
    pub field: Field,
}

impl fmt::Display for DowncastExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "(downcast {} to {} in {})",
            self.enum_place, &self.field, self.base,
        )
    }
}

impl PartialEq for DowncastExpr {
    fn eq(&self, other: &Self) -> bool {
        (&*self.base, &*self.enum_place, &self.field)
            == (&*other.base, &*other.enum_place, &other.field)
    }
}

impl Hash for DowncastExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&*self.base, &*self.enum_place, &self.field).hash(state);
    }
}

#[derive(
    Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialOrd, Ord, PartialEq, Eq, Hash,
)]
pub enum CastKind {
    BVIntoInt(BitVector),
    IntIntoBV(BitVector),
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct Cast {
    pub kind: CastKind,
    pub base: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for Cast {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cast<{:?}>({})", self.kind, self.base)
    }
}

impl PartialEq for Cast {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.base == other.base
    }
}

impl Hash for Cast {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (&self.kind, &*self.base).hash(state);
    }
}

#[derive(Debug, Clone, Eq, serde::Serialize, serde::Deserialize, PartialOrd, Ord)]
pub struct SnapApp {
    pub base: Box<Expr>,
    pub position: Position,
}

impl fmt::Display for SnapApp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "snap({})", self.base)
    }
}

impl PartialEq for SnapApp {
    fn eq(&self, other: &Self) -> bool {
        self.base == other.base
    }
}

impl Hash for SnapApp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.base).hash(state);
    }
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UnaryOpKind::Not => write!(f, "!"),
            UnaryOpKind::Minus => write!(f, "-"),
        }
    }
}

impl fmt::Display for BinaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOpKind::EqCmp => write!(f, "=="),
            BinaryOpKind::NeCmp => write!(f, "!="),
            BinaryOpKind::GtCmp => write!(f, ">"),
            BinaryOpKind::GeCmp => write!(f, ">="),
            BinaryOpKind::LtCmp => write!(f, "<"),
            BinaryOpKind::LeCmp => write!(f, "<="),
            BinaryOpKind::Add => write!(f, "+"),
            BinaryOpKind::Sub => write!(f, "-"),
            BinaryOpKind::Mul => write!(f, "*"),
            BinaryOpKind::Div => write!(f, "\\"),
            BinaryOpKind::Mod => write!(f, "%"),
            BinaryOpKind::And => write!(f, "&&"),
            BinaryOpKind::Or => write!(f, "||"),
            BinaryOpKind::Implies => write!(f, "==>"),
            BinaryOpKind::BitAnd => write!(f, "&"),
            BinaryOpKind::BitOr => write!(f, "|"),
            BinaryOpKind::BitXor => write!(f, "^"),
            BinaryOpKind::Shl => write!(f, "<<"),
            BinaryOpKind::LShr => write!(f, ">>>"),
            BinaryOpKind::AShr => write!(f, ">>"),
            BinaryOpKind::Min => write!(f, "min"),
            BinaryOpKind::Max => write!(f, "max"),
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Const::Bool(val) => write!(f, "{}", val),
            Const::Int(val) => write!(f, "{}", val),
            Const::BigInt(ref val) => write!(f, "{}", val),
            Const::Float(val) => write!(f, "{:?}", val),
            Const::BitVector(val) => write!(f, "{:?}", val),
            Const::FnPtr => write!(f, "FnPtr"),
        }
    }
}

pub trait ExprIterator {
    /// Conjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn conjoin(&mut self) -> Expr;

    /// Disjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn disjoin(&mut self) -> Expr;
}

impl<T> ExprIterator for T
where
    T: Iterator<Item = Expr>,
{
    fn conjoin(&mut self) -> Expr {
        fn rfold<T>(s: &mut T) -> Expr
        where
            T: Iterator<Item = Expr>,
        {
            if let Some(conjunct) = s.next() {
                Expr::and(conjunct, rfold(s))
            } else {
                true.into()
            }
        }
        rfold(self)
    }

    fn disjoin(&mut self) -> Expr {
        fn rfold<T>(s: &mut T) -> Expr
        where
            T: Iterator<Item = Expr>,
        {
            if let Some(conjunct) = s.next() {
                Expr::or(conjunct, rfold(s))
            } else {
                false.into()
            }
        }
        rfold(self)
    }
}
