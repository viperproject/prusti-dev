// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(clippy::many_single_char_names)]

use super::super::borrows::Borrow;
use crate::polymorphic::ast::*;

impl Expr {
    /// Apply the closure to all places in the expression.
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
}

pub trait ExprFolder: Sized {
    fn fold(&mut self, e: Expr) -> Expr {
        default_fold_expr(self, e)
    }

    fn fold_boxed(&mut self, e: Box<Expr>) -> Box<Expr> {
        box self.fold(*e)
    }

    fn fold_local(&mut self, v: LocalVar, p: Position) -> Expr {
        Expr::Local( Local {
            variable: v,
            position: p,
        })
    }

    fn fold_variant(&mut self, base: Box<Expr>, variant: Field, p: Position) -> Expr {
        Expr::Variant ( Variant {
            base: self.fold_boxed(base),
            variant_index: variant,
            position: p,
        })
    }

    fn fold_field(&mut self, receiver: Box<Expr>, field: Field, pos: Position) -> Expr {
        Expr::Field( FieldExpr {
            base: self.fold_boxed(receiver),
            field: field,
            position: pos,
        })
    }

    fn fold_addr_of(&mut self, e: Box<Expr>, t: Type, p: Position) -> Expr {
        Expr::AddrOf( AddrOf {
            base: self.fold_boxed(e),
            addr_type: t,
            position: p,
        })
    }

    fn fold_const(&mut self, x: Const, p: Position) -> Expr {
        Expr::Const ( ConstExpr {
            value: x,
            position: p,
        })
    }

    fn fold_labelled_old(&mut self, label: String, body: Box<Expr>, pos: Position) -> Expr {
        Expr::LabelledOld (LabelledOld {
            label: label,
            base: self.fold_boxed(body),
            position: pos,
        })
    }

    fn fold_magic_wand(
        &mut self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow: Option<Borrow>,
        pos: Position,
    ) -> Expr {
        Expr::MagicWand (MagicWand {
            left: self.fold_boxed(lhs),
            right: self.fold_boxed(rhs),
            borrow: borrow,
            position: pos,
        })
    }

    fn fold_predicate_access_predicate(
        &mut self,
        typ: Type,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        Expr::PredicateAccessPredicate( PredicateAccessPredicate {
            predicate_type: typ,
            argument: self.fold_boxed(arg),
            permission: perm_amount,
            position: pos,
        })
    }

    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        Expr::FieldAccessPredicate( FieldAccessPredicate {
            base: self.fold_boxed(receiver),
            permission: perm_amount,
            position: pos,
        })
    }

    fn fold_unary_op(&mut self, x: UnaryOpKind, y: Box<Expr>, p: Position) -> Expr {
        Expr::UnaryOp( UnaryOp {
            op_kind: x,
            argument: self.fold_boxed(y),
            position: p,
        })
    }

    fn fold_bin_op(
        &mut self,
        kind: BinOpKind,
        first: Box<Expr>,
        second: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::BinOp( BinOp {
            op_kind: kind,
            left: self.fold_boxed(first),
            right: self.fold_boxed(second),
            position: pos,
        })
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
        Expr::Unfolding( Unfolding {
            predicate_name: name,
            arguments: args.into_iter().map(|e| self.fold(e)).collect(),
            base: self.fold_boxed(expr),
            permission: perm,
            variant: variant,
            position: pos,
        })
    }

    fn fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::Cond( Cond {
            guard: self.fold_boxed(guard),
            then_expr: self.fold_boxed(then_expr),
            else_expr: self.fold_boxed(else_expr),
            position: pos,
        })
    }

    fn fold_forall(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::ForAll( ForAll {
            variables: x,
            triggers: y,
            body: self.fold_boxed(z),
            position: p,
        })
    }

    fn fold_exists(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::ForAll( ForAll {
            variables: x,
            triggers: y,
            body: self.fold_boxed(z),
            position: p,
        })
    }

    fn fold_let_expr(
        &mut self,
        var: LocalVar,
        expr: Box<Expr>,
        body: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::LetExpr( LetExpr {
            variable: var,
            def: self.fold_boxed(expr),
            body: self.fold_boxed(body),
            position: pos,
        })
    }

    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Expr {
        Expr::FuncApp( FuncApp {
            function_name: name,
            arguments: args.into_iter().map(|e| self.fold(e)).collect(),
            formal_arguments: formal_args,
            return_type: return_type,
            position: pos,
        })
    }

    fn fold_domain_func_app(&mut self, func: DomainFunc, args: Vec<Expr>, pos: Position) -> Expr {
        Expr::DomainFuncApp ( DomainFuncApp {
            domain_function: func,
            arguments: args.into_iter().map(|e| self.fold(e)).collect(),
            position: pos,
        })
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
            pos
        )
    }
    */
    fn fold_inhale_exhale(
        &mut self,
        inhale_expr: Box<Expr>,
        exhale_expr: Box<Expr>,
        pos: Position,
    ) -> Expr {
        Expr::InhaleExhale( InhaleExhale {
            inhale_expr: self.fold_boxed(inhale_expr),
            exhale_expr: self.fold_boxed(exhale_expr),
            position: pos,
        })
    }

    fn fold_downcast(&mut self, base: Box<Expr>, enum_place: Box<Expr>, field: Field) -> Expr {
        Expr::Downcast( DowncastExpr {
            base: self.fold_boxed(base),
            enum_place: self.fold_boxed(enum_place),
            field: field,
        })
    }

    fn fold_snap_app(&mut self, e: Box<Expr>, p: Position) -> Expr {
        Expr::SnapApp( SnapApp {
            base: self.fold_boxed(e),
            position: p,
        })
    }

    fn fold_container_op(
        &mut self,
        kind: ContainerOpKind,
        l: Box<Expr>,
        r: Box<Expr>,
        p: Position,
    ) -> Expr {
        Expr::ContainerOp( ContainerOp {
            op_kind: kind,
            left: self.fold_boxed(l),
            right: self.fold_boxed(r),
            position: p,
        })
    }

    fn fold_seq(&mut self, t: Type, elems: Vec<Expr>, p: Position) -> Expr {
        Expr::Seq( Seq {
            typ: t,
            elements: elems.into_iter().map(|e| self.fold(e)).collect(),
            position: p,
        })
    }
}

pub fn default_fold_expr<T: ExprFolder>(this: &mut T, e: Expr) -> Expr {
    match e {
        Expr::Local( Local {variable, position} ) => this.fold_local(variable, position),
        Expr::Variant( Variant {base, variant_index, position} ) => this.fold_variant(base, variant_index, position),
        Expr::Field( FieldExpr {base, field, position} ) => this.fold_field(base, field, position),
        Expr::AddrOf( AddrOf {base, addr_type, position} ) => this.fold_addr_of(base, addr_type, position),
        Expr::Const( ConstExpr {value, position} ) => this.fold_const(value, position),
        Expr::LabelledOld( LabelledOld {label, base, position} ) => this.fold_labelled_old(label, base, position),
        Expr::MagicWand(MagicWand {left, right, borrow, position} )=> this.fold_magic_wand(left, right, borrow, position),
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {predicate_type, argument, permission, position} ) => {
            this.fold_predicate_access_predicate(predicate_type, argument, permission, position)
        },
        Expr::FieldAccessPredicate(FieldAccessPredicate {base, permission, position} ) => this.fold_field_access_predicate(base, permission, position),
        Expr::UnaryOp(UnaryOp {op_kind, argument, position} ) => this.fold_unary_op(op_kind, argument, position),
        Expr::BinOp(BinOp {op_kind, left, right, position} ) => this.fold_bin_op(op_kind, left, right, position),
        Expr::Unfolding(Unfolding {predicate_name, arguments, base, permission, variant, position} ) => {
            this.fold_unfolding(predicate_name, arguments, base, permission, variant, position)
        },
        Expr::Cond(Cond {guard, then_expr, else_expr, position} ) => this.fold_cond(guard, then_expr, else_expr, position),
        Expr::ForAll(ForAll {variables, triggers, body, position} ) => this.fold_forall(variables, triggers, body, position),
        Expr::Exists(Exists {variables, triggers, body, position} ) => this.fold_exists(variables, triggers, body, position),
        Expr::LetExpr(LetExpr {variable, def, body, position} ) => this.fold_let_expr(variable, def, body, position),
        Expr::FuncApp(FuncApp {function_name, arguments, formal_arguments, return_type, position} ) => this.fold_func_app(function_name, arguments, formal_arguments, return_type, position),
        Expr::DomainFuncApp(DomainFuncApp {domain_function, arguments, position} ) => this.fold_domain_func_app(domain_function, arguments, position),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(InhaleExhale {inhale_expr, exhale_expr, position} ) => this.fold_inhale_exhale(inhale_expr, exhale_expr, position),
        Expr::Downcast(DowncastExpr {base, enum_place, field} ) => this.fold_downcast(base, enum_place, field),
        Expr::SnapApp(SnapApp {base, position} ) => this.fold_snap_app(base, position),
        Expr::ContainerOp(ContainerOp {op_kind, left, right, position} ) => this.fold_container_op(op_kind, left, right, position),
        Expr::Seq(Seq {typ, elements, position} ) => this.fold_seq(typ, elements, position),
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

    fn walk_local(&mut self, var: &LocalVar, _pos: &Position) {
        self.walk_local_var(var);
    }
    fn walk_variant(&mut self, base: &Expr, variant: &Field, _pos: &Position) {
        self.walk(base);
        self.walk_type(&variant.typ);
    }
    fn walk_field(&mut self, receiver: &Expr, field: &Field, _pos: &Position) {
        self.walk(receiver);
        self.walk_type(&field.typ);
    }
    fn walk_addr_of(&mut self, receiver: &Expr, typ: &Type, _pos: &Position) {
        self.walk(receiver);
        self.walk_type(typ);
    }
    fn walk_const(&mut self, _const: &Const, _pos: &Position) {}
    fn walk_labelled_old(&mut self, _label: &str, body: &Expr, _pos: &Position) {
        self.walk(body);
    }
    fn walk_magic_wand(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        _borrow: &Option<Borrow>,
        _pos: &Position,
    ) {
        self.walk(lhs);
        self.walk(rhs);
    }
    fn walk_predicate_access_predicate(
        &mut self,
        _typ: &Type,
        arg: &Expr,
        _perm_amount: PermAmount,
        _pos: &Position,
    ) {
        self.walk(arg)
    }
    fn walk_field_access_predicate(
        &mut self,
        receiver: &Expr,
        _perm_amount: PermAmount,
        _pos: &Position,
    ) {
        self.walk(receiver)
    }
    fn walk_unary_op(&mut self, _op: UnaryOpKind, arg: &Expr, _pos: &Position) {
        self.walk(arg)
    }
    fn walk_bin_op(&mut self, _op: BinOpKind, arg1: &Expr, arg2: &Expr, _pos: &Position) {
        self.walk(arg1);
        self.walk(arg2);
    }
    fn walk_unfolding(
        &mut self,
        _name: &str,
        args: &Vec<Expr>,
        body: &Expr,
        _perm: PermAmount,
        _variant: &MaybeEnumVariantIndex,
        _pos: &Position,
    ) {
        for arg in args {
            self.walk(arg);
        }
        self.walk(body);
    }
    fn walk_cond(&mut self, guard: &Expr, then_expr: &Expr, else_expr: &Expr, _pos: &Position) {
        self.walk(guard);
        self.walk(then_expr);
        self.walk(else_expr);
    }
    fn walk_forall(
        &mut self,
        vars: &Vec<LocalVar>,
        _triggers: &Vec<Trigger>,
        body: &Expr,
        _pos: &Position,
    ) {
        for var in vars {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_exists(
        &mut self,
        vars: &Vec<LocalVar>,
        _triggers: &Vec<Trigger>,
        body: &Expr,
        _pos: &Position,
    ) {
        for var in vars {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_let_expr(&mut self, bound_var: &LocalVar, expr: &Expr, body: &Expr, _pos: &Position) {
        self.walk_local_var(bound_var);
        self.walk(expr);
        self.walk(body);
    }
    fn walk_func_app(
        &mut self,
        _name: &str,
        args: &Vec<Expr>,
        formal_args: &Vec<LocalVar>,
        return_type: &Type,
        _pos: &Position,
    ) {
        for arg in args {
            self.walk(arg)
        }
        for arg in formal_args {
            self.walk_local_var(arg);
        }
        self.walk_type(return_type);
    }
    fn walk_domain_func_app(&mut self, func: &DomainFunc, args: &Vec<Expr>, _pos: &Position) {
        for arg in args {
            self.walk(arg)
        }
        for arg in &func.formal_args {
            self.walk_local_var(arg)
        }
        self.walk_type(&func.return_type);
    }
    /* TODO
    fn walk_domain_func_app(
        &mut self,
        _function_name: &String,
        args: &Vec<Expr>,
        formal_args: &Vec<LocalVar>,
        _return_type: &Type,
        _domain_name: &String,
        _pos: &Position) {
        for arg in args {
            self.walk(arg)
        }
        for arg in formal_args {
            self.walk_local_var(arg)
        }
    }
    */
    fn walk_inhale_exhale(&mut self, inhale_expr: &Expr, exhale_expr: &Expr, _pos: &Position) {
        self.walk(inhale_expr);
        self.walk(exhale_expr);
    }

    fn walk_downcast(&mut self, base: &Expr, enum_place: &Expr, _field: &Field) {
        self.walk(base);
        self.walk(enum_place);
    }
    fn walk_snap_app(&mut self, expr: &Expr, _pos: &Position) {
        self.walk(expr);
    }

    fn walk_container_op(&mut self, _kind: &ContainerOpKind, l: &Expr, r: &Expr, _p: &Position) {
        self.walk(l);
        self.walk(r);
    }

    fn walk_seq(&mut self, typ: &Type, elems: &[Expr], _pos: &Position) {
        for elem in elems {
            self.walk(elem);
        }
        self.walk_type(typ);
    }
}

pub fn default_walk_expr<T: ExprWalker>(this: &mut T, e: &Expr) {
    match *e {
        Expr::Local( Local {ref variable, ref position} ) => this.walk_local(variable, position),
        Expr::Variant( Variant {ref base, ref variant_index, ref position} ) => this.walk_variant(base, variant_index, position),
        Expr::Field( FieldExpr {ref base, ref field, ref position} ) => this.walk_field(base, field, position),
        Expr::AddrOf( AddrOf {ref base, ref addr_type, ref position} ) => this.walk_addr_of(base, addr_type, position),
        Expr::Const( ConstExpr {ref value, ref position} ) => this.walk_const(value, position),
        Expr::LabelledOld( LabelledOld {ref label, ref base, ref position} ) => this.walk_labelled_old(label, base, position),
        Expr::MagicWand(MagicWand {ref left, ref right, ref borrow, ref position} ) => this.walk_magic_wand(left, right, borrow, position),
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {ref predicate_type, ref argument, permission, ref position} ) => {
            this.walk_predicate_access_predicate(predicate_type, argument, permission, position)
        },
        Expr::FieldAccessPredicate(FieldAccessPredicate {ref base, permission, ref position} ) => this.walk_field_access_predicate(base, permission, position),
        Expr::UnaryOp(UnaryOp {op_kind, ref argument, ref position} ) => this.walk_unary_op(op_kind, argument, position),
        Expr::BinOp(BinOp {op_kind, ref left, ref right, ref position} ) => this.walk_bin_op(op_kind, left, right, position),
        Expr::Unfolding(Unfolding {ref predicate_name, ref arguments, ref base, permission, ref variant, ref position} ) => {
            this.walk_unfolding(predicate_name, arguments, base, permission, variant, position)
        },
        Expr::Cond(Cond {ref guard, ref then_expr, ref else_expr, ref position} ) => this.walk_cond(guard, then_expr, else_expr, position),
        Expr::ForAll(ForAll {ref variables, ref triggers, ref body, ref position} ) => this.walk_forall(variables, triggers, body, position),
        Expr::Exists(Exists {ref variables, ref triggers, ref body, ref position} ) => this.walk_exists(variables, triggers, body, position),
        Expr::LetExpr(LetExpr {ref variable, ref def, ref body, ref position} ) => this.walk_let_expr(variable, def, body, position),
        Expr::FuncApp(FuncApp {ref function_name, ref arguments, ref formal_arguments, ref return_type, ref position} ) => this.walk_func_app(function_name, arguments, formal_arguments, return_type, position),
        Expr::DomainFuncApp(DomainFuncApp {ref domain_function, ref arguments, ref position} ) => this.walk_domain_func_app(domain_function, arguments, position),
        // TODO Expr::DomainFuncApp(ref u, ref v, ref w, ref x, ref y,ref p) => this.walk_domain_func_app(u, v, w, x,y,p),
        Expr::InhaleExhale(InhaleExhale {ref inhale_expr, ref exhale_expr, ref position} ) => this.walk_inhale_exhale(inhale_expr, exhale_expr, position),
        Expr::Downcast(DowncastExpr {ref base, ref enum_place, ref field} ) => this.walk_downcast(base, enum_place, field),
        Expr::SnapApp(SnapApp {ref base, ref position} ) => this.walk_snap_app(base, position),
        Expr::ContainerOp(ContainerOp {ref op_kind, ref left, ref right, ref position} ) => this.walk_container_op(op_kind, left, right, position),
        Expr::Seq(Seq {ref typ, ref elements, ref position} ) => this.walk_seq(typ, elements, position),
    }
}

pub trait FallibleExprFolder: Sized {
    type Error;

    fn fallible_fold(&mut self, e: Expr) -> Result<Expr, Self::Error> {
        default_fallible_fold_expr(self, e)
    }

    fn fallible_fold_boxed(&mut self, e: Box<Expr>) -> Result<Box<Expr>, Self::Error> {
        Ok(box self.fallible_fold(*e)?)
    }

    fn fallible_fold_local(&mut self, v: LocalVar, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::Local( Local {
            variable: v,
            position: p,
        }))
    }

    fn fallible_fold_variant(
        &mut self,
        base: Box<Expr>,
        variant: Field,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Variant( Variant {
            base: self.fallible_fold_boxed(base)?,
            variant_index: variant,
            position: p,
        }))
    }

    fn fallible_fold_field(
        &mut self,
        receiver: Box<Expr>,
        field: Field,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Field (FieldExpr {
            base: self.fallible_fold_boxed(receiver)?,
            field: field,
            position: pos,
        }))
    }

    fn fallible_fold_addr_of(
        &mut self,
        e: Box<Expr>,
        t: Type,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::AddrOf( AddrOf {
            base: self.fallible_fold_boxed(e)?,
            addr_type: t,
            position: p,
        }))
    }

    fn fallible_fold_const(&mut self, x: Const, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::Const( ConstExpr {
            value: x,
            position: p,
        }))
    }

    fn fallible_fold_labelled_old(
        &mut self,
        label: String,
        body: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::LabelledOld( LabelledOld {
            label: label,
            base: self.fallible_fold_boxed(body)?,
            position: pos,
        }))
    }

    fn fallible_fold_magic_wand(
        &mut self,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow: Option<Borrow>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::MagicWand( MagicWand {
            left: self.fallible_fold_boxed(lhs)?,
            right: self.fallible_fold_boxed(rhs)?,
            borrow: borrow,
            position: pos,
        }))
    }

    fn fallible_fold_predicate_access_predicate(
        &mut self,
        typ: Type,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::PredicateAccessPredicate( PredicateAccessPredicate {
            predicate_type: typ,
            argument: self.fallible_fold_boxed(arg)?,
            permission: perm_amount,
            position: pos,
        }))
    }

    fn fallible_fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::FieldAccessPredicate( FieldAccessPredicate {
            base: self.fallible_fold_boxed(receiver)?,
            permission: perm_amount,
            position: pos,
        }))
    }

    fn fallible_fold_unary_op(
        &mut self,
        x: UnaryOpKind,
        y: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::UnaryOp( UnaryOp {
            op_kind: x,
            argument: self.fallible_fold_boxed(y)?,
            position: p,
        }))
    }

    fn fallible_fold_bin_op(
        &mut self,
        kind: BinOpKind,
        first: Box<Expr>,
        second: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::BinOp( BinOp {
            op_kind: kind,
            left: self.fallible_fold_boxed(first)?,
            right: self.fallible_fold_boxed(second)?,
            position: pos,
        }))
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
        Ok(Expr::Unfolding( Unfolding {
            predicate_name: name,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            base: self.fallible_fold_boxed(expr)?,
            permission: perm,
            variant: variant,
            position: pos,
        }))
    }

    fn fallible_fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Cond( Cond {
            guard: self.fallible_fold_boxed(guard)?,
            then_expr: self.fallible_fold_boxed(then_expr)?,
            else_expr: self.fallible_fold_boxed(else_expr)?,
            position: pos,
        }))
    }

    fn fallible_fold_forall(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::ForAll( ForAll {
            variables: x,
            triggers: y,
            body: self.fallible_fold_boxed(z)?,
            position: p,
        }))
    }

    fn fallible_fold_exists(
        &mut self,
        x: Vec<LocalVar>,
        y: Vec<Trigger>,
        z: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Exists( Exists {
            variables: x,
            triggers: y,
            body: self.fallible_fold_boxed(z)?,
            position: p,
        }))
    }

    fn fallible_fold_let_expr(
        &mut self,
        var: LocalVar,
        expr: Box<Expr>,
        body: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::LetExpr( LetExpr {
            variable: var,
            def: self.fallible_fold_boxed(expr)?,
            body: self.fallible_fold_boxed(body)?,
            position: pos,
        }))
    }

    fn fallible_fold_func_app(
        &mut self,
        name: String,
        args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::FuncApp( FuncApp {
            function_name: name,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            formal_arguments: formal_args,
            return_type: return_type,
            position: pos,
        }))
    }

    fn fallible_fold_domain_func_app(
        &mut self,
        func: DomainFunc,
        args: Vec<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::DomainFuncApp( DomainFuncApp {
            domain_function: func,
            arguments: args.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            position: pos,
        }))
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
        Ok(Expr::InhaleExhale( InhaleExhale {
            inhale_expr: self.fallible_fold_boxed(inhale)?,
            exhale_expr: self.fallible_fold_boxed(exhale)?,
            position: pos,
        }))
    }

    fn fallible_fold_downcast(
        &mut self,
        base: Box<Expr>,
        enum_expr: Box<Expr>,
        field: Field,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Downcast( DowncastExpr {
            base: self.fallible_fold_boxed(base)?,
            enum_place: self.fallible_fold_boxed(enum_expr)?,
            field: field,
        }))
    }

    fn fallible_fold_snap_app(&mut self, e: Box<Expr>, p: Position) -> Result<Expr, Self::Error> {
        Ok(Expr::SnapApp( SnapApp {
            base: self.fallible_fold_boxed(e)?,
            position: p,
        }))
    }

    fn fallible_fold_container_op(
        &mut self,
        kind: ContainerOpKind,
        l: Box<Expr>,
        r: Box<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::ContainerOp( ContainerOp {
            op_kind: kind,
            left: self.fallible_fold_boxed(l)?,
            right: self.fallible_fold_boxed(r)?,
            position: p,
        }))
    }

    fn fallible_fold_seq(
        &mut self,
        ty: Type,
        elems: Vec<Expr>,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(Expr::Seq( Seq {
            typ: ty,
            elements: elems
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            position: p,
        }))
    }
}

pub fn default_fallible_fold_expr<U, T: FallibleExprFolder<Error = U>>(
    this: &mut T,
    e: Expr,
) -> Result<Expr, U> {
    match e {
        Expr::Local( Local {variable, position} ) => this.fallible_fold_local(variable, position),
        Expr::Variant( Variant {base, variant_index, position} ) => this.fallible_fold_variant(base, variant_index, position),
        Expr::Field( FieldExpr {base, field, position} ) => this.fallible_fold_field(base, field, position),
        Expr::AddrOf( AddrOf {base, addr_type, position} ) => this.fallible_fold_addr_of(base, addr_type, position),
        Expr::Const( ConstExpr {value, position} ) => this.fallible_fold_const(value, position),
        Expr::LabelledOld( LabelledOld {label, base, position} ) => this.fallible_fold_labelled_old(label, base, position),
        Expr::MagicWand(MagicWand {left, right, borrow, position} ) => this.fallible_fold_magic_wand(left, right, borrow, position),
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {predicate_type, argument, permission, position} ) => {
            this.fallible_fold_predicate_access_predicate(predicate_type, argument, permission, position)
        },
        Expr::FieldAccessPredicate(FieldAccessPredicate {base, permission, position} ) => this.fallible_fold_field_access_predicate(base, permission, position),
        Expr::UnaryOp(UnaryOp {op_kind, argument, position} ) => this.fallible_fold_unary_op(op_kind, argument, position),
        Expr::BinOp(BinOp {op_kind, left, right, position} ) => this.fallible_fold_bin_op(op_kind, left, right, position),
        Expr::Unfolding(Unfolding {predicate_name, arguments, base, permission, variant, position} ) => {
            this.fallible_fold_unfolding(predicate_name, arguments, base, permission, variant, position)
        },
        Expr::Cond(Cond {guard, then_expr, else_expr, position} ) => this.fallible_fold_cond(guard, then_expr, else_expr, position),
        Expr::ForAll(ForAll {variables, triggers, body, position} ) => this.fallible_fold_forall(variables, triggers, body, position),
        Expr::Exists(Exists {variables, triggers, body, position} ) => this.fallible_fold_exists(variables, triggers, body, position),
        Expr::LetExpr(LetExpr {variable, def, body, position} ) => this.fallible_fold_let_expr(variable, def, body, position),
        Expr::FuncApp(FuncApp {function_name, arguments, formal_arguments, return_type, position} ) => this.fallible_fold_func_app(function_name, arguments, formal_arguments, return_type, position),
        Expr::DomainFuncApp(DomainFuncApp {domain_function, arguments, position} ) => this.fallible_fold_domain_func_app(domain_function, arguments, position),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fallible_fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(InhaleExhale {inhale_expr, exhale_expr, position} ) => this.fallible_fold_inhale_exhale(inhale_expr, exhale_expr, position),
        Expr::Downcast(DowncastExpr {base, enum_place, field} ) => this.fallible_fold_downcast(base, enum_place, field),
        Expr::SnapApp(SnapApp {base, position} ) => this.fallible_fold_snap_app(base, position),
        Expr::ContainerOp(ContainerOp {op_kind, left, right, position} ) => this.fallible_fold_container_op(op_kind, left, right, position),
        Expr::Seq(Seq {typ, elements, position} ) => this.fallible_fold_seq(typ, elements, position),
    }
}
