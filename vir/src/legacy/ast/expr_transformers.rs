// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// This module is full of functions matching `Expr`s and reassembling them with one field changed
// (e.g. new position), so we feel it's ok to use single-digit identifiers there
#![allow(clippy::many_single_char_names)]

use super::super::borrows::Borrow;
use crate::legacy::ast::*;
use std::mem;

impl Expr {
    /// Apply the closure to all places in the expression.
    #[must_use]
    pub fn fold_places<F>(self, f: F) -> Expr
    where
        F: Fn(Expr) -> Expr,
    {
        struct PlaceFolder<F>
        where
            F: Fn(Expr) -> Expr,
        {
            f: F,
        }
        impl<F> ExprFolder for PlaceFolder<F>
        where
            F: Fn(Expr) -> Expr,
        {
            fn fold(&mut self, e: Expr) -> Expr {
                if e.is_place() {
                    (self.f)(e)
                } else {
                    default_fold_expr(self, e)
                }
            }
            // TODO: Handle triggers?
        }
        PlaceFolder { f }.fold(self)
    }

    /// Apply the closure to all expressions.
    #[must_use]
    pub fn fold_expr<F>(self, f: F) -> Expr
    where
        F: Fn(Expr) -> Expr,
    {
        struct ExprFolderImpl<F>
        where
            F: Fn(Expr) -> Expr,
        {
            f: F,
        }
        impl<F> ExprFolder for ExprFolderImpl<F>
        where
            F: Fn(Expr) -> Expr,
        {
            fn fold(&mut self, e: Expr) -> Expr {
                let new_expr = default_fold_expr(self, e);
                (self.f)(new_expr)
            }
        }
        ExprFolderImpl { f }.fold(self)
    }

    /// Visit each position.
    pub fn visit_positions<F: FnMut(&Position)>(&self, visitor: F) {
        struct PositionsVisitor<F: FnMut(&Position)> {
            visitor: F,
        }
        impl<F: FnMut(&Position)> ExprWalker for PositionsVisitor<F> {
            fn walk_position(&mut self, pos: &Position) {
                (self.visitor)(pos);
            }
        }
        PositionsVisitor { visitor }.walk(self);
    }

    /// Mutably visit each position.
    pub fn visit_positions_mut<F: FnMut(&mut Position)>(&mut self, visitor: F) {
        struct PositionsMutVisitor<G: FnMut(&mut Position)> {
            visitor: G,
        }
        impl<G: FnMut(&mut Position)> ExprFolder for PositionsMutVisitor<G> {
            fn fold_position(&mut self, mut pos: Position) -> Position {
                (self.visitor)(&mut pos);
                pos
            }
        }
        let expr = mem::replace(self, true.into());
        *self = PositionsMutVisitor { visitor }.fold(expr);
    }
}

pub trait ExprFolder: Sized {
    fn fold(&mut self, e: Expr) -> Expr {
        default_fold_expr(self, e)
    }

    #[allow(clippy::boxed_local)]
    fn fold_boxed(&mut self, e: Box<Expr>) -> Box<Expr> {
        Box::new(self.fold(*e))
    }

    fn fold_local(&mut self, v: LocalVar, p: Position) -> Expr {
        Expr::Local(v, self.fold_position(p))
    }
    fn fold_variant(&mut self, base: Box<Expr>, variant: Field, p: Position) -> Expr {
        Expr::Variant(self.fold_boxed(base), variant, self.fold_position(p))
    }
    fn fold_field(&mut self, receiver: Box<Expr>, field: Field, pos: Position) -> Expr {
        Expr::Field(self.fold_boxed(receiver), field, self.fold_position(pos))
    }
    fn fold_addr_of(&mut self, e: Box<Expr>, t: Type, p: Position) -> Expr {
        Expr::AddrOf(self.fold_boxed(e), t, self.fold_position(p))
    }
    fn fold_const(&mut self, x: Const, p: Position) -> Expr {
        Expr::Const(x, self.fold_position(p))
    }
    fn fold_labelled_old(&mut self, label: String, body: Box<Expr>, pos: Position) -> Expr {
        Expr::LabelledOld(label, self.fold_boxed(body), self.fold_position(pos))
    }
    fn fold_magic_wand(
        &mut self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow: Option<Borrow>,
        pos: Position,
    ) -> Expr {
        Expr::MagicWand(
            self.fold_boxed(lhs),
            self.fold_boxed(rhs),
            borrow,
            self.fold_position(pos),
        )
    }
    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        Expr::PredicateAccessPredicate(
            name,
            self.fold_boxed(arg),
            perm_amount,
            self.fold_position(pos),
        )
    }
    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        Expr::FieldAccessPredicate(
            self.fold_boxed(receiver),
            perm_amount,
            self.fold_position(pos),
        )
    }
    fn fold_unary_op(&mut self, x: UnaryOpKind, y: Box<Expr>, p: Position) -> Expr {
        Expr::UnaryOp(x, self.fold_boxed(y), self.fold_position(p))
    }
    fn fold_bin_op(
        &mut self,
        kind: BinaryOpKind,
        first: Box<Expr>,
        second: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::BinOp(
            kind,
            self.fold_boxed(first),
            self.fold_boxed(second),
            self.fold_position(pos),
        )
    }
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Expr {
        Expr::Unfolding(
            name,
            args.into_iter().map(|e| self.fold(e)).collect(),
            self.fold_boxed(expr),
            perm,
            variant,
            self.fold_position(pos),
        )
    }
    fn fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::Cond(
            self.fold_boxed(guard),
            self.fold_boxed(then_expr),
            self.fold_boxed(else_expr),
            self.fold_position(pos),
        )
    }
    fn fold_forall(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::ForAll(x, y, self.fold_boxed(z), self.fold_position(p))
    }
    fn fold_exists(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::Exists(x, y, self.fold_boxed(z), self.fold_position(p))
    }
    fn fold_let_expr(
        &mut self,
        var: LocalVar,
        expr: Box<Expr>,
        body: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::LetExpr(
            var,
            self.fold_boxed(expr),
            self.fold_boxed(body),
            self.fold_position(pos),
        )
    }
    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Expr {
        Expr::FuncApp(
            name,
            args.into_iter().map(|e| self.fold(e)).collect(),
            formal_args,
            return_type,
            self.fold_position(pos),
        )
    }
    fn fold_domain_func_app(&mut self, func: DomainFunc, args: Vec<Expr>, pos: Position) -> Expr {
        Expr::DomainFuncApp(
            func,
            args.into_iter().map(|e| self.fold(e)).collect(),
            self.fold_position(pos),
        )
    }
    /* TODO
    fn fold_domain_func_app(
        &mut self,
        function_name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        domain_name: String,
        pos: Position,
    ) -> Expr {
        Expr::DomainFuncApp(
            function_name,
            args.into_iter().map(|e| self.fold(e)).collect(),
            formal_args,
            return_type,
            domain_name,
            self.fold_position(pos)
        )
    }
    */
    fn fold_inhale_exhale(
        &mut self,
        inhale_expr: Box<Expr>,
        exhale_expr: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::InhaleExhale(
            self.fold_boxed(inhale_expr),
            self.fold_boxed(exhale_expr),
            self.fold_position(pos),
        )
    }

    fn fold_downcast(&mut self, base: Box<Expr>, enum_place: Box<Expr>, field: Field) -> Expr {
        Expr::Downcast(self.fold_boxed(base), self.fold_boxed(enum_place), field)
    }
    fn fold_snap_app(&mut self, e: Box<Expr>, p: Position) -> Expr {
        Expr::SnapApp(self.fold_boxed(e), self.fold_position(p))
    }

    fn fold_container_op(
        &mut self,
        kind: ContainerOpKind,
        l: Box<Expr>,
        r: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::ContainerOp(
            kind,
            self.fold_boxed(l),
            self.fold_boxed(r),
            self.fold_position(p),
        )
    }

    fn fold_seq(&mut self, t: Type, elems: Vec<Expr>, p: Position) -> Expr {
        Expr::Seq(
            t,
            elems.into_iter().map(|e| self.fold(e)).collect(),
            self.fold_position(p),
        )
    }

    fn fold_map(&mut self, t: Type, elems: Vec<Expr>, p: Position) -> Expr {
        Expr::Map(
            t,
            elems.into_iter().map(|e| self.fold(e)).collect(),
            self.fold_position(p),
        )
    }

    fn fold_cast(&mut self, kind: CastKind, base: Box<Expr>, p: Position) -> Expr {
        Expr::Cast(kind, base, self.fold_position(p))
    }

    fn fold_position(&mut self, p: Position) -> Position {
        p
    }
}

pub fn default_fold_expr<T: ExprFolder>(this: &mut T, e: Expr) -> Expr {
    match e {
        Expr::Local(v, p) => this.fold_local(v, p),
        Expr::Variant(base, variant, p) => this.fold_variant(base, variant, p),
        Expr::Field(e, f, p) => this.fold_field(e, f, p),
        Expr::AddrOf(e, t, p) => this.fold_addr_of(e, t, p),
        Expr::Const(x, p) => this.fold_const(x, p),
        Expr::LabelledOld(x, y, p) => this.fold_labelled_old(x, y, p),
        Expr::MagicWand(x, y, b, p) => this.fold_magic_wand(x, y, b, p),
        Expr::PredicateAccessPredicate(x, y, z, p) => {
            this.fold_predicate_access_predicate(x, y, z, p)
        }
        Expr::FieldAccessPredicate(x, y, p) => this.fold_field_access_predicate(x, y, p),
        Expr::UnaryOp(x, y, p) => this.fold_unary_op(x, y, p),
        Expr::BinOp(x, y, z, p) => this.fold_bin_op(x, y, z, p),
        Expr::Unfolding(x, y, z, perm, variant, p) => {
            this.fold_unfolding(x, y, z, perm, variant, p)
        }
        Expr::Cond(x, y, z, p) => this.fold_cond(x, y, z, p),
        Expr::ForAll(x, y, z, p) => this.fold_forall(x, y, z, p),
        Expr::Exists(x, y, z, p) => this.fold_exists(x, y, z, p),
        Expr::LetExpr(x, y, z, p) => this.fold_let_expr(x, y, z, p),
        Expr::FuncApp(x, y, z, k, p) => this.fold_func_app(x, y, z, k, p),
        Expr::DomainFuncApp(x, y, p) => this.fold_domain_func_app(x, y, p),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(x, y, p) => this.fold_inhale_exhale(x, y, p),
        Expr::Downcast(b, p, f) => this.fold_downcast(b, p, f),
        Expr::SnapApp(e, p) => this.fold_snap_app(e, p),
        Expr::ContainerOp(x, y, z, p) => this.fold_container_op(x, y, z, p),
        Expr::Seq(x, y, p) => this.fold_seq(x, y, p),
        Expr::Map(x, y, p) => this.fold_map(x, y, p),
        Expr::Cast(kind, base, p) => this.fold_cast(kind, base, p),
    }
}

pub trait ExprWalker: Sized {
    fn walk(&mut self, expr: &Expr) {
        default_walk_expr(self, expr);
    }

    fn walk_type(&mut self, _typ: &Type) {}
    fn walk_local_var(&mut self, var: &LocalVar) {
        self.walk_type(&var.typ);
    }

    fn walk_local(&mut self, var: &LocalVar, pos: &Position) {
        self.walk_local_var(var);
        self.walk_position(pos);
    }
    fn walk_variant(&mut self, base: &Expr, variant: &Field, pos: &Position) {
        self.walk(base);
        self.walk_type(&variant.typ);
        self.walk_position(pos);
    }
    fn walk_field(&mut self, receiver: &Expr, field: &Field, pos: &Position) {
        self.walk(receiver);
        self.walk_type(&field.typ);
        self.walk_position(pos);
    }
    fn walk_addr_of(&mut self, receiver: &Expr, typ: &Type, pos: &Position) {
        self.walk(receiver);
        self.walk_type(typ);
        self.walk_position(pos);
    }
    fn walk_const(&mut self, _const: &Const, pos: &Position) {
        self.walk_position(pos);
    }
    fn walk_labelled_old(&mut self, _label: &str, body: &Expr, pos: &Position) {
        self.walk(body);
        self.walk_position(pos);
    }
    fn walk_magic_wand(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        _borrow: &Option<Borrow>,
        pos: &Position,
    ) {
        self.walk(lhs);
        self.walk(rhs);
        self.walk_position(pos);
    }
    fn walk_predicate_access_predicate(
        &mut self,
        _name: &str,
        arg: &Expr,
        _perm_amount: PermAmount,
        pos: &Position,
    ) {
        self.walk(arg);
        self.walk_position(pos);
    }
    fn walk_field_access_predicate(
        &mut self,
        receiver: &Expr,
        _perm_amount: PermAmount,
        pos: &Position,
    ) {
        self.walk(receiver);
        self.walk_position(pos);
    }
    fn walk_unary_op(&mut self, _op: UnaryOpKind, arg: &Expr, pos: &Position) {
        self.walk(arg);
        self.walk_position(pos);
    }
    fn walk_bin_op(&mut self, _op: BinaryOpKind, arg1: &Expr, arg2: &Expr, pos: &Position) {
        self.walk(arg1);
        self.walk(arg2);
        self.walk_position(pos);
    }
    fn walk_unfolding(
        &mut self,
        _name: &str,
        args: &[Expr],
        body: &Expr,
        _perm: PermAmount,
        _variant: &MaybeEnumVariantIndex,
        pos: &Position,
    ) {
        for arg in args {
            self.walk(arg);
        }
        self.walk(body);
        self.walk_position(pos);
    }
    fn walk_cond(&mut self, guard: &Expr, then_expr: &Expr, else_expr: &Expr, pos: &Position) {
        self.walk(guard);
        self.walk(then_expr);
        self.walk(else_expr);
        self.walk_position(pos);
    }
    fn walk_forall(
        &mut self,
        vars: &[LocalVar],
        triggers: &[Trigger],
        body: &Expr,
        pos: &Position,
    ) {
        for set in triggers {
            for expr in set.elements() {
                self.walk(expr);
            }
        }
        for var in vars {
            self.walk_local_var(var);
        }
        self.walk(body);
        self.walk_position(pos);
    }
    fn walk_exists(
        &mut self,
        vars: &[LocalVar],
        triggers: &[Trigger],
        body: &Expr,
        pos: &Position,
    ) {
        for set in triggers {
            for expr in set.elements() {
                self.walk(expr);
            }
        }
        for var in vars {
            self.walk_local_var(var);
        }
        self.walk(body);
        self.walk_position(pos);
    }
    fn walk_let_expr(&mut self, bound_var: &LocalVar, expr: &Expr, body: &Expr, pos: &Position) {
        self.walk_local_var(bound_var);
        self.walk(expr);
        self.walk(body);
        self.walk_position(pos);
    }
    fn walk_func_app(
        &mut self,
        _name: &str,
        args: &[Expr],
        formal_args: &[LocalVar],
        return_type: &Type,
        pos: &Position,
    ) {
        for arg in args {
            self.walk(arg)
        }
        for arg in formal_args {
            self.walk_local_var(arg);
        }
        self.walk_type(return_type);
        self.walk_position(pos);
    }
    fn walk_domain_func_app(&mut self, func: &DomainFunc, args: &[Expr], pos: &Position) {
        for arg in args {
            self.walk(arg)
        }
        for arg in &func.formal_args {
            self.walk_local_var(arg)
        }
        self.walk_type(&func.return_type);
        self.walk_position(pos);
    }
    /* TODO
    fn walk_domain_func_app(
        &mut self,
        _function_name: &String,
        args: &Vec<Expr>,
        formal_args: &Vec<LocalVar>,
        _return_type: &Type,
        _domain_name: &String,
        pos: &Position) {
        for arg in args {
            self.walk(arg)
        }
        for arg in formal_args {
            self.walk_local_var(arg)
        }
        self.walk_position(pos);
    }
    */
    fn walk_inhale_exhale(&mut self, inhale_expr: &Expr, exhale_expr: &Expr, pos: &Position) {
        self.walk(inhale_expr);
        self.walk(exhale_expr);
        self.walk_position(pos);
    }

    fn walk_downcast(&mut self, base: &Expr, enum_place: &Expr, _field: &Field) {
        self.walk(base);
        self.walk(enum_place);
    }
    fn walk_snap_app(&mut self, expr: &Expr, pos: &Position) {
        self.walk(expr);
        self.walk_position(pos);
    }

    fn walk_container_op(&mut self, _kind: &ContainerOpKind, l: &Expr, r: &Expr, pos: &Position) {
        self.walk(l);
        self.walk(r);
        self.walk_position(pos);
    }

    fn walk_seq(&mut self, typ: &Type, elems: &[Expr], pos: &Position) {
        for elem in elems {
            self.walk(elem);
        }
        self.walk_type(typ);
        self.walk_position(pos);
    }

    fn walk_map(&mut self, typ: &Type, elems: &[Expr], pos: &Position) {
        for elem in elems {
            self.walk(elem);
        }
        self.walk_type(typ);
        self.walk_position(pos);
    }

    fn walk_cast(&mut self, _kind: &CastKind, base: &Expr, pos: &Position) {
        self.walk(base);
        self.walk_position(pos);
    }

    fn walk_position(&mut self, _pos: &Position) {}
}

pub fn default_walk_expr<T: ExprWalker>(this: &mut T, e: &Expr) {
    match *e {
        Expr::Local(ref v, ref p) => this.walk_local(v, p),
        Expr::Variant(ref base, ref variant, ref p) => this.walk_variant(base, variant, p),
        Expr::Field(ref e, ref f, ref p) => this.walk_field(e, f, p),
        Expr::AddrOf(ref e, ref t, ref p) => this.walk_addr_of(e, t, p),
        Expr::Const(ref x, ref p) => this.walk_const(x, p),
        Expr::LabelledOld(ref x, ref y, ref p) => this.walk_labelled_old(x, y, p),
        Expr::MagicWand(ref x, ref y, ref b, ref p) => this.walk_magic_wand(x, y, b, p),
        Expr::PredicateAccessPredicate(ref x, ref y, z, ref p) => {
            this.walk_predicate_access_predicate(x, y, z, p)
        }
        Expr::FieldAccessPredicate(ref x, y, ref p) => this.walk_field_access_predicate(x, y, p),
        Expr::UnaryOp(x, ref y, ref p) => this.walk_unary_op(x, y, p),
        Expr::BinOp(x, ref y, ref z, ref p) => this.walk_bin_op(x, y, z, p),
        Expr::Unfolding(ref x, ref y, ref z, perm, ref variant, ref p) => {
            this.walk_unfolding(x, y, z, perm, variant, p)
        }
        Expr::Cond(ref x, ref y, ref z, ref p) => this.walk_cond(x, y, z, p),
        Expr::ForAll(ref x, ref y, ref z, ref p) => this.walk_forall(x, y, z, p),
        Expr::Exists(ref x, ref y, ref z, ref p) => this.walk_exists(x, y, z, p),
        Expr::LetExpr(ref x, ref y, ref z, ref p) => this.walk_let_expr(x, y, z, p),
        Expr::FuncApp(ref x, ref y, ref z, ref k, ref p) => this.walk_func_app(x, y, z, k, p),
        Expr::DomainFuncApp(ref x, ref y, ref p) => this.walk_domain_func_app(x, y, p),
        // TODO Expr::DomainFuncApp(ref u, ref v, ref w, ref x, ref y,ref p) => this.walk_domain_func_app(u, v, w, x,y,p),
        Expr::InhaleExhale(ref x, ref y, ref p) => this.walk_inhale_exhale(x, y, p),
        Expr::Downcast(ref b, ref p, ref f) => this.walk_downcast(b, p, f),
        Expr::SnapApp(ref e, ref p) => this.walk_snap_app(e, p),
        Expr::ContainerOp(ref kind, ref l, ref r, ref p) => this.walk_container_op(kind, l, r, p),
        Expr::Seq(ref ty, ref elems, ref p) => this.walk_seq(ty, elems, p),
        Expr::Map(ref ty, ref elems, ref p) => this.walk_map(ty, elems, p),
        Expr::Cast(ref kind, ref base, ref p) => this.walk_cast(kind, base, p),
    }
}

pub trait FallibleExprFolder: Sized {
    type Error;

    fn fallible_fold(&mut self, e: Expr) -> Result<Expr, Self::Error> {
        default_fallible_fold_expr(self, e)
    }

    #[allow(clippy::boxed_local)]
    fn fallible_fold_boxed(&mut self, e: Box<Expr>) -> Result<Box<Expr>, Self::Error> {
        Ok(Box::new(self.fallible_fold(*e)?))
    }

    fn fallible_fold_local(&mut self, v: LocalVar, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::Local(v, p))
    }
    fn fallible_fold_variant(
        &mut self,
        base: Box<Expr>,
        variant: Field,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Variant(self.fallible_fold_boxed(base)?, variant, p))
    }
    fn fallible_fold_field(
        &mut self,
        receiver: Box<Expr>,
        field: Field,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Field(self.fallible_fold_boxed(receiver)?, field, pos))
    }
    fn fallible_fold_addr_of(
        &mut self,
        e: Box<Expr>,
        t: Type,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::AddrOf(self.fallible_fold_boxed(e)?, t, p))
    }
    fn fallible_fold_const(&mut self, x: Const, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::Const(x, p))
    }
    fn fallible_fold_labelled_old(
        &mut self,
        label: String,
        body: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::LabelledOld(
            label,
            self.fallible_fold_boxed(body)?,
            pos,
        ))
    }
    fn fallible_fold_magic_wand(
        &mut self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow: Option<Borrow>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::MagicWand(
            self.fallible_fold_boxed(lhs)?,
            self.fallible_fold_boxed(rhs)?,
            borrow,
            pos,
        ))
    }
    fn fallible_fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::PredicateAccessPredicate(
            name,
            self.fallible_fold_boxed(arg)?,
            perm_amount,
            pos,
        ))
    }
    fn fallible_fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::FieldAccessPredicate(
            self.fallible_fold_boxed(receiver)?,
            perm_amount,
            pos,
        ))
    }
    fn fallible_fold_unary_op(
        &mut self,
        x: UnaryOpKind,
        y: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::UnaryOp(x, self.fallible_fold_boxed(y)?, p))
    }
    fn fallible_fold_bin_op(
        &mut self,
        kind: BinaryOpKind,
        first: Box<Expr>,
        second: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::BinOp(
            kind,
            self.fallible_fold_boxed(first)?,
            self.fallible_fold_boxed(second)?,
            pos,
        ))
    }
    fn fallible_fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: PermAmount,
        variant: MaybeEnumVariantIndex,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Unfolding(
            name,
            args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            self.fallible_fold_boxed(expr)?,
            perm,
            variant,
            pos,
        ))
    }
    fn fallible_fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Cond(
            self.fallible_fold_boxed(guard)?,
            self.fallible_fold_boxed(then_expr)?,
            self.fallible_fold_boxed(else_expr)?,
            pos,
        ))
    }
    fn fallible_fold_forall(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::ForAll(x, y, self.fallible_fold_boxed(z)?, p))
    }
    fn fallible_fold_exists(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Exists(x, y, self.fallible_fold_boxed(z)?, p))
    }
    fn fallible_fold_let_expr(
        &mut self,
        var: LocalVar,
        expr: Box<Expr>,
        body: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::LetExpr(
            var,
            self.fallible_fold_boxed(expr)?,
            self.fallible_fold_boxed(body)?,
            pos,
        ))
    }
    fn fallible_fold_func_app(
        &mut self,
        name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::FuncApp(
            name,
            args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            formal_args,
            return_type,
            pos,
        ))
    }
    fn fallible_fold_domain_func_app(
        &mut self,
        func: DomainFunc,
        args: Vec<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::DomainFuncApp(
            func,
            args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            pos,
        ))
    }
    /* TODO
    fn fallible_fold_domain_func_app(
        &mut self,
        function_name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        domain_name: String,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
            Ok(Expr::DomainFuncApp(
            function_name,
            args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            formal_args,
            return_type,
            domain_name,
            pos
        ))
    }
    */
    fn fallible_fold_inhale_exhale(
        &mut self,
        inhale: Box<Expr>,
        exhale: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::InhaleExhale(
            self.fallible_fold_boxed(inhale)?,
            self.fallible_fold_boxed(exhale)?,
            pos,
        ))
    }

    fn fallible_fold_downcast(
        &mut self,
        base: Box<Expr>,
        enum_expr: Box<Expr>,
        field: Field,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Downcast(
            self.fallible_fold_boxed(base)?,
            self.fallible_fold_boxed(enum_expr)?,
            field,
        ))
    }
    fn fallible_fold_snap_app(&mut self, e: Box<Expr>, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::SnapApp(self.fallible_fold_boxed(e)?, p))
    }

    fn fallible_fold_container_op(
        &mut self,
        kind: ContainerOpKind,
        l: Box<Expr>,
        r: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::ContainerOp(
            kind,
            self.fallible_fold_boxed(l)?,
            self.fallible_fold_boxed(r)?,
            p,
        ))
    }

    fn fallible_fold_seq(
        &mut self,
        ty: Type,
        elems: Vec<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Seq(
            ty,
            elems
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            p,
        ))
    }

    fn fallible_fold_map(
        &mut self,
        ty: Type,
        elems: Vec<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Map(
            ty,
            elems
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            p,
        ))
    }

    fn fallible_fold_cast(
        &mut self,
        kind: CastKind,
        base: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Cast(kind, self.fallible_fold_boxed(base)?, p))
    }
}

pub fn default_fallible_fold_expr<U, T: FallibleExprFolder<Error = U>>(
    this: &mut T,
    e: Expr,
) -> Result<Expr, U> {
    match e {
        Expr::Local(v, p) => this.fallible_fold_local(v, p),
        Expr::Variant(base, variant, p) => this.fallible_fold_variant(base, variant, p),
        Expr::Field(e, f, p) => this.fallible_fold_field(e, f, p),
        Expr::AddrOf(e, t, p) => this.fallible_fold_addr_of(e, t, p),
        Expr::Const(x, p) => this.fallible_fold_const(x, p),
        Expr::LabelledOld(x, y, p) => this.fallible_fold_labelled_old(x, y, p),
        Expr::MagicWand(x, y, b, p) => this.fallible_fold_magic_wand(x, y, b, p),
        Expr::PredicateAccessPredicate(x, y, z, p) => {
            this.fallible_fold_predicate_access_predicate(x, y, z, p)
        }
        Expr::FieldAccessPredicate(x, y, p) => this.fallible_fold_field_access_predicate(x, y, p),
        Expr::UnaryOp(x, y, p) => this.fallible_fold_unary_op(x, y, p),
        Expr::BinOp(x, y, z, p) => this.fallible_fold_bin_op(x, y, z, p),
        Expr::Unfolding(x, y, z, perm, variant, p) => {
            this.fallible_fold_unfolding(x, y, z, perm, variant, p)
        }
        Expr::Cond(x, y, z, p) => this.fallible_fold_cond(x, y, z, p),
        Expr::ForAll(x, y, z, p) => this.fallible_fold_forall(x, y, z, p),
        Expr::Exists(x, y, z, p) => this.fallible_fold_exists(x, y, z, p),
        Expr::LetExpr(x, y, z, p) => this.fallible_fold_let_expr(x, y, z, p),
        Expr::FuncApp(x, y, z, k, p) => this.fallible_fold_func_app(x, y, z, k, p),
        Expr::DomainFuncApp(x, y, p) => this.fallible_fold_domain_func_app(x, y, p),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fallible_fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(x, y, p) => this.fallible_fold_inhale_exhale(x, y, p),
        Expr::Downcast(b, p, f) => this.fallible_fold_downcast(b, p, f),
        Expr::SnapApp(e, p) => this.fallible_fold_snap_app(e, p),
        Expr::ContainerOp(x, y, z, p) => this.fallible_fold_container_op(x, y, z, p),
        Expr::Seq(x, y, p) => this.fallible_fold_seq(x, y, p),
        Expr::Map(x, y, p) => this.fallible_fold_map(x, y, p),
        Expr::Cast(kind, base, p) => this.fallible_fold_cast(kind, base, p),
    }
}
