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

    fn fold_local(&mut self, local: Local) -> Expr {
        Expr::Local(local)
    }

    fn fold_variant(&mut self, Variant {base, variant_index, position}: Variant) -> Expr {
        Expr::Variant ( Variant {
            base: self.fold_boxed(base),
            variant_index,
            position,
        })
    }

    fn fold_field(&mut self, FieldExpr {base, field, position}: FieldExpr) -> Expr {
        Expr::Field( FieldExpr {
            base: self.fold_boxed(base),
            field,
            position,
        })
    }

    fn fold_addr_of(&mut self, AddrOf {base, addr_type, position}: AddrOf) -> Expr {
        Expr::AddrOf( AddrOf {
            base: self.fold_boxed(base),
            addr_type,
            position,
        })
    }

    fn fold_const(&mut self, const_expr: ConstExpr) -> Expr {
        Expr::Const (const_expr)
    }

    fn fold_labelled_old(&mut self, LabelledOld {label, base, position}: LabelledOld) -> Expr {
        Expr::LabelledOld (LabelledOld {
            label,
            base: self.fold_boxed(base),
            position,
        })
    }

    fn fold_magic_wand(&mut self, MagicWand {left, right, borrow, position}: MagicWand) -> Expr {
        Expr::MagicWand (MagicWand {
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            borrow,
            position,
        })
    }

    fn fold_predicate_access_predicate(&mut self, PredicateAccessPredicate {predicate_type, argument, permission, position}: PredicateAccessPredicate) -> Expr {
        Expr::PredicateAccessPredicate( PredicateAccessPredicate {
            predicate_type,
            argument: self.fold_boxed(argument),
            permission,
            position,
        })
    }

    fn fold_field_access_predicate(&mut self, FieldAccessPredicate {base, permission, position}: FieldAccessPredicate) -> Expr {
        Expr::FieldAccessPredicate( FieldAccessPredicate {
            base: self.fold_boxed(base),
            permission,
            position,
        })
    }

    fn fold_unary_op(&mut self, UnaryOp {op_kind, argument, position}: UnaryOp) -> Expr {
        Expr::UnaryOp( UnaryOp {
            op_kind,
            argument: self.fold_boxed(argument),
            position,
        })
    }

    fn fold_bin_op(&mut self, BinOp {op_kind, left, right, position}: BinOp) -> Expr {
        Expr::BinOp( BinOp {
            op_kind,
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            position,
        })
    }

    fn fold_unfolding(&mut self, Unfolding {predicate_name, arguments, base, permission, variant, position}: Unfolding) -> Expr {
        Expr::Unfolding( Unfolding {
            predicate_name,
            arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
            base: self.fold_boxed(base),
            permission,
            variant,
            position,
        })
    }

    fn fold_cond(&mut self, Cond {guard, then_expr, else_expr, position}: Cond) -> Expr {
        Expr::Cond( Cond {
            guard: self.fold_boxed(guard),
            then_expr: self.fold_boxed(then_expr),
            else_expr: self.fold_boxed(else_expr),
            position,
        })
    }

    fn fold_forall(&mut self, ForAll {variables, triggers, body, position}: ForAll) -> Expr {
        Expr::ForAll( ForAll {
            variables,
            triggers,
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_exists(&mut self, Exists {variables, triggers, body, position}: Exists) -> Expr {
        Expr::ForAll( ForAll {
            variables,
            triggers,
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_let_expr(&mut self, LetExpr {variable, def, body, position}: LetExpr) -> Expr {
        Expr::LetExpr( LetExpr {
            variable,
            def: self.fold_boxed(def),
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_func_app(&mut self, FuncApp {function_name, arguments, formal_arguments, return_type, position}: FuncApp) -> Expr {
        Expr::FuncApp( FuncApp {
            function_name,
            arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
            formal_arguments,
            return_type,
            position,
        })
    }

    fn fold_domain_func_app(&mut self, DomainFuncApp {domain_function, arguments, position}: DomainFuncApp) -> Expr {
        Expr::DomainFuncApp ( DomainFuncApp {
            domain_function,
            arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
            position,
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
    fn fold_inhale_exhale(&mut self, InhaleExhale {inhale_expr, exhale_expr, position}: InhaleExhale) -> Expr {
        Expr::InhaleExhale( InhaleExhale {
            inhale_expr: self.fold_boxed(inhale_expr),
            exhale_expr: self.fold_boxed(exhale_expr),
            position,
        })
    }

    fn fold_downcast(&mut self, DowncastExpr {base, enum_place, field}: DowncastExpr) -> Expr {
        Expr::Downcast( DowncastExpr {
            base: self.fold_boxed(base),
            enum_place: self.fold_boxed(enum_place),
            field,
        })
    }

    fn fold_snap_app(&mut self, SnapApp {base, position}: SnapApp) -> Expr {
        Expr::SnapApp( SnapApp {
            base: self.fold_boxed(base),
            position,
        })
    }

    fn fold_container_op(&mut self, ContainerOp {op_kind, left, right, position}: ContainerOp) -> Expr {
        Expr::ContainerOp( ContainerOp {
            op_kind,
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            position,
        })
    }

    fn fold_seq(&mut self, Seq {typ, elements, position}: Seq) -> Expr {
        Expr::Seq( Seq {
            typ,
            elements: elements.into_iter().map(|e| self.fold(e)).collect(),
            position,
        })
    }
}

pub fn default_fold_expr<T: ExprFolder>(this: &mut T, e: Expr) -> Expr {
    match e {
        Expr::Local(local) => this.fold_local(local),
        Expr::Variant(variant) => this.fold_variant(variant),
        Expr::Field(field_expr) => this.fold_field(field_expr),
        Expr::AddrOf(addr_of) => this.fold_addr_of(addr_of),
        Expr::Const(const_expr) => this.fold_const(const_expr),
        Expr::LabelledOld(labelled_old) => this.fold_labelled_old(labelled_old),
        Expr::MagicWand(magic_wand)=> this.fold_magic_wand(magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => this.fold_predicate_access_predicate(predicate_access_predicate),
        Expr::FieldAccessPredicate(field_access_predicate) => this.fold_field_access_predicate(field_access_predicate),
        Expr::UnaryOp(unary_op) => this.fold_unary_op(unary_op),
        Expr::BinOp(bin_op) => this.fold_bin_op(bin_op),
        Expr::Unfolding(unfolding) => this.fold_unfolding(unfolding),
        Expr::Cond(cond) => this.fold_cond(cond),
        Expr::ForAll(forall) => this.fold_forall(forall),
        Expr::Exists(exists) => this.fold_exists(exists),
        Expr::LetExpr(let_expr) => this.fold_let_expr(let_expr),
        Expr::FuncApp(func_app) => this.fold_func_app(func_app),
        Expr::DomainFuncApp(domain_func_app) => this.fold_domain_func_app(domain_func_app),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(inhale_exhale) => this.fold_inhale_exhale(inhale_exhale),
        Expr::Downcast(downcast_expr) => this.fold_downcast(downcast_expr),
        Expr::SnapApp(snap_app) => this.fold_snap_app(snap_app),
        Expr::ContainerOp(container_op) => this.fold_container_op(container_op),
        Expr::Seq(seq) => this.fold_seq(seq),
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

    fn walk_local(&mut self, Local {variable, ..}: &Local) {
        self.walk_local_var(variable);
    }
    fn walk_variant(&mut self, Variant {base, variant_index, ..}: &Variant) {
        self.walk(base);
        self.walk_type(&variant_index.typ);
    }
    fn walk_field(&mut self, FieldExpr {base, field, ..}: &FieldExpr) {
        self.walk(base);
        self.walk_type(&field.typ);
    }
    fn walk_addr_of(&mut self, AddrOf {base, addr_type, ..}: &AddrOf) {
        self.walk(base);
        self.walk_type(addr_type);
    }
    fn walk_const(&mut self, _const_expr: &ConstExpr) {}
    fn walk_labelled_old(&mut self, LabelledOld {base, ..}: &LabelledOld) {
        self.walk(base);
    }
    fn walk_magic_wand(&mut self, MagicWand {left, right, ..}: &MagicWand) {
        self.walk(left);
        self.walk(right);
    }
    fn walk_predicate_access_predicate(&mut self, PredicateAccessPredicate {argument, ..}: &PredicateAccessPredicate) {
        self.walk(argument);
    }
    fn walk_field_access_predicate(&mut self, FieldAccessPredicate {base, ..}: &FieldAccessPredicate) {
        self.walk(base);
    }
    fn walk_unary_op(&mut self, UnaryOp {argument, ..}: &UnaryOp) {
        self.walk(argument)
    }
    fn walk_bin_op(&mut self, BinOp {left, right, ..}: &BinOp) {
        self.walk(left);
        self.walk(right);
    }
    fn walk_unfolding(&mut self, Unfolding {arguments, base, ..}: &Unfolding) {
        for arg in arguments {
            self.walk(arg);
        }
        self.walk(base);
    }
    fn walk_cond(&mut self, Cond {guard, then_expr, else_expr, ..}: &Cond) {
        self.walk(guard);
        self.walk(then_expr);
        self.walk(else_expr);
    }
    fn walk_forall(&mut self, ForAll {variables, body, ..}: &ForAll) {
        for var in variables {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_exists(&mut self, Exists {variables, body, ..}: &Exists) {
        for var in variables {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_let_expr(&mut self, LetExpr {variable, def, body, ..}: &LetExpr) {
        self.walk_local_var(variable);
        self.walk(def);
        self.walk(body);
    }
    fn walk_func_app(&mut self, FuncApp {arguments, formal_arguments, return_type, ..}: &FuncApp) {
        for arg in arguments {
            self.walk(arg)
        }
        for arg in formal_arguments {
            self.walk_local_var(arg);
        }
        self.walk_type(return_type);
    }
    fn walk_domain_func_app(&mut self, DomainFuncApp {domain_function, arguments, ..}: &DomainFuncApp) {
        for arg in arguments {
            self.walk(arg)
        }
        for arg in &domain_function.formal_args {
            self.walk_local_var(arg)
        }
        self.walk_type(&domain_function.return_type);
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
    fn walk_inhale_exhale(&mut self, InhaleExhale {inhale_expr, exhale_expr, ..}: &InhaleExhale) {
        self.walk(inhale_expr);
        self.walk(exhale_expr);
    }

    fn walk_downcast(&mut self, DowncastExpr {base, enum_place, ..}: &DowncastExpr) {
        self.walk(base);
        self.walk(enum_place);
    }
    fn walk_snap_app(&mut self, SnapApp {base, ..}: &SnapApp) {
        self.walk(base);
    }

    fn walk_container_op(&mut self, ContainerOp {left, right, ..}: &ContainerOp) {
        self.walk(left);
        self.walk(right);
    }

    fn walk_seq(&mut self, Seq {typ, elements, ..}: &Seq) {
        for elem in elements {
            self.walk(elem);
        }
        self.walk_type(typ);
    }
}

pub fn default_walk_expr<T: ExprWalker>(this: &mut T, e: &Expr) {
    match e {
        Expr::Local(local) => this.walk_local(&local),
        Expr::Variant(variant) => this.walk_variant(&variant),
        Expr::Field(field_expr) => this.walk_field(&field_expr),
        Expr::AddrOf(addr_of) => this.walk_addr_of(&addr_of),
        Expr::Const(const_expr) => this.walk_const(&const_expr),
        Expr::LabelledOld(labelled_old) => this.walk_labelled_old(&labelled_old),
        Expr::MagicWand(magic_wand) => this.walk_magic_wand(&magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => this.walk_predicate_access_predicate(&predicate_access_predicate),
        Expr::FieldAccessPredicate(field_access_predicate) => this.walk_field_access_predicate(&field_access_predicate),
        Expr::UnaryOp(unary_op) => this.walk_unary_op(&unary_op),
        Expr::BinOp(bin_op) => this.walk_bin_op(&bin_op),
        Expr::Unfolding(unfolding) => this.walk_unfolding(&unfolding),
        Expr::Cond(cond) => this.walk_cond(&cond),
        Expr::ForAll(forall) => this.walk_forall(&forall),
        Expr::Exists(exists) => this.walk_exists(&exists),
        Expr::LetExpr(let_expr) => this.walk_let_expr(&let_expr),
        Expr::FuncApp(func_app) => this.walk_func_app(&func_app),
        Expr::DomainFuncApp(domain_func_app) => this.walk_domain_func_app(&domain_func_app),
        // TODO Expr::DomainFuncApp(ref u, ref v, ref w, ref x, ref y,ref p) => this.walk_domain_func_app(u, v, w, x,y,p),
        Expr::InhaleExhale(inhale_exhale) => this.walk_inhale_exhale(&inhale_exhale),
        Expr::Downcast(downcast_expr) => this.walk_downcast(&downcast_expr),
        Expr::SnapApp(snap_app) => this.walk_snap_app(&snap_app),
        Expr::ContainerOp(container_op) => this.walk_container_op(&container_op),
        Expr::Seq(seq) => this.walk_seq(&seq),
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

    fn fallible_fold_local(&mut self, local: Local) -> Result<Expr, Self::Error> {
        Ok(Expr::Local(local))
    }

    fn fallible_fold_variant(&mut self, Variant {base, variant_index, position}: Variant) -> Result<Expr, Self::Error> {
        Ok(Expr::Variant( Variant {
            base: self.fallible_fold_boxed(base)?,
            variant_index,
            position,
        }))
    }

    fn fallible_fold_field(&mut self, FieldExpr {base, field, position}: FieldExpr) -> Result<Expr, Self::Error> {
        Ok(Expr::Field (FieldExpr {
            base: self.fallible_fold_boxed(base)?,
            field,
            position,
        }))
    }

    fn fallible_fold_addr_of(&mut self, AddrOf {base, addr_type, position}: AddrOf) -> Result<Expr, Self::Error> {
        Ok(Expr::AddrOf( AddrOf {
            base: self.fallible_fold_boxed(base)?,
            addr_type,
            position,
        }))
    }

    fn fallible_fold_const(&mut self, const_expr: ConstExpr) -> Result<Expr, Self::Error> {
        Ok(Expr::Const(const_expr))
    }

    fn fallible_fold_labelled_old(&mut self, LabelledOld {label, base, position}: LabelledOld) -> Result<Expr, Self::Error> {
        Ok(Expr::LabelledOld( LabelledOld {
            label,
            base: self.fallible_fold_boxed(base)?,
            position,
        }))
    }

    fn fallible_fold_magic_wand(&mut self, MagicWand {left, right, borrow, position}: MagicWand) -> Result<Expr, Self::Error> {
        Ok(Expr::MagicWand( MagicWand {
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            borrow,
            position,
        }))
    }

    fn fallible_fold_predicate_access_predicate(&mut self, PredicateAccessPredicate {predicate_type, argument, permission, position}: PredicateAccessPredicate) -> Result<Expr, Self::Error> {
        Ok(Expr::PredicateAccessPredicate( PredicateAccessPredicate {
            predicate_type,
            argument: self.fallible_fold_boxed(argument)?,
            permission,
            position,
        }))
    }

    fn fallible_fold_field_access_predicate(&mut self, FieldAccessPredicate {base, permission, position}: FieldAccessPredicate) -> Result<Expr, Self::Error> {
        Ok(Expr::FieldAccessPredicate( FieldAccessPredicate {
            base: self.fallible_fold_boxed(base)?,
            permission,
            position,
        }))
    }

    fn fallible_fold_unary_op(&mut self, UnaryOp {op_kind, argument, position}: UnaryOp) -> Result<Expr, Self::Error> {
        Ok(Expr::UnaryOp( UnaryOp {
            op_kind,
            argument: self.fallible_fold_boxed(argument)?,
            position,
        }))
    }

    fn fallible_fold_bin_op(&mut self, BinOp {op_kind, left, right, position}: BinOp) -> Result<Expr, Self::Error> {
        Ok(Expr::BinOp( BinOp {
            op_kind,
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            position,
        }))
    }

    fn fallible_fold_unfolding(&mut self, Unfolding {predicate_name, arguments, base, permission, variant, position}: Unfolding) -> Result<Expr, Self::Error> {
        Ok(Expr::Unfolding( Unfolding {
            predicate_name,
            arguments: arguments.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            base: self.fallible_fold_boxed(base)?,
            permission,
            variant,
            position,
        }))
    }

    fn fallible_fold_cond(&mut self, Cond {guard, then_expr, else_expr, position}: Cond) -> Result<Expr, Self::Error> {
        Ok(Expr::Cond( Cond {
            guard: self.fallible_fold_boxed(guard)?,
            then_expr: self.fallible_fold_boxed(then_expr)?,
            else_expr: self.fallible_fold_boxed(else_expr)?,
            position,
        }))
    }

    fn fallible_fold_forall(&mut self, ForAll {variables, triggers, body, position}: ForAll) -> Result<Expr, Self::Error> {
        Ok(Expr::ForAll( ForAll {
            variables,
            triggers,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_exists(&mut self, Exists {variables, triggers, body, position}: Exists) -> Result<Expr, Self::Error> {
        Ok(Expr::Exists( Exists {
            variables,
            triggers,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_let_expr(&mut self, LetExpr {variable, def, body, position}: LetExpr) -> Result<Expr, Self::Error> {
        Ok(Expr::LetExpr( LetExpr {
            variable,
            def: self.fallible_fold_boxed(def)?,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_func_app(&mut self, FuncApp {function_name, arguments, formal_arguments, return_type, position}: FuncApp) -> Result<Expr, Self::Error> {
        Ok(Expr::FuncApp( FuncApp {
            function_name,
            arguments: arguments.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            formal_arguments,
            return_type,
            position,
        }))
    }

    fn fallible_fold_domain_func_app(&mut self, DomainFuncApp {domain_function, arguments, position}: DomainFuncApp) -> Result<Expr, Self::Error> {
        Ok(Expr::DomainFuncApp( DomainFuncApp {
            domain_function,
            arguments: arguments.into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            position,
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
    fn fallible_fold_inhale_exhale(&mut self, InhaleExhale {inhale_expr, exhale_expr, position}: InhaleExhale) -> Result<Expr, Self::Error> {
        Ok(Expr::InhaleExhale( InhaleExhale {
            inhale_expr: self.fallible_fold_boxed(inhale_expr)?,
            exhale_expr: self.fallible_fold_boxed(exhale_expr)?,
            position,
        }))
    }

    fn fallible_fold_downcast(&mut self, DowncastExpr {base, enum_place, field}: DowncastExpr) -> Result<Expr, Self::Error> {
        Ok(Expr::Downcast( DowncastExpr {
            base: self.fallible_fold_boxed(base)?,
            enum_place: self.fallible_fold_boxed(enum_place)?,
            field,
        }))
    }

    fn fallible_fold_snap_app(&mut self, SnapApp {base, position}: SnapApp) -> Result<Expr, Self::Error> {
        Ok(Expr::SnapApp( SnapApp {
            base: self.fallible_fold_boxed(base)?,
            position,
        }))
    }

    fn fallible_fold_container_op(&mut self, ContainerOp {op_kind, left, right, position}: ContainerOp) -> Result<Expr, Self::Error> {
        Ok(Expr::ContainerOp( ContainerOp {
            op_kind,
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            position,
        }))
    }

    fn fallible_fold_seq(&mut self, Seq {typ, elements, position}: Seq) -> Result<Expr, Self::Error> {
        Ok(Expr::Seq( Seq {
            typ,
            elements: elements
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            position,
        }))
    }
}

pub fn default_fallible_fold_expr<U, T: FallibleExprFolder<Error = U>>(
    this: &mut T,
    e: Expr,
) -> Result<Expr, U> {
    match e {
        Expr::Local(local) => this.fallible_fold_local(local),
        Expr::Variant(variant) => this.fallible_fold_variant(variant),
        Expr::Field(field) => this.fallible_fold_field(field),
        Expr::AddrOf(addr_of) => this.fallible_fold_addr_of(addr_of),
        Expr::Const(const_expr) => this.fallible_fold_const(const_expr),
        Expr::LabelledOld(labelled_old) => this.fallible_fold_labelled_old(labelled_old),
        Expr::MagicWand(magic_wand) => this.fallible_fold_magic_wand(magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => this.fallible_fold_predicate_access_predicate(predicate_access_predicate),
        Expr::FieldAccessPredicate(field_access_predicate) => this.fallible_fold_field_access_predicate(field_access_predicate),
        Expr::UnaryOp(unary_op) => this.fallible_fold_unary_op(unary_op),
        Expr::BinOp(bin_op) => this.fallible_fold_bin_op(bin_op),
        Expr::Unfolding(unfolding) => this.fallible_fold_unfolding(unfolding),
        Expr::Cond(cond) => this.fallible_fold_cond(cond),
        Expr::ForAll(forall) => this.fallible_fold_forall(forall),
        Expr::Exists(exists) => this.fallible_fold_exists(exists),
        Expr::LetExpr(let_expr) => this.fallible_fold_let_expr(let_expr),
        Expr::FuncApp(func_app) => this.fallible_fold_func_app(func_app),
        Expr::DomainFuncApp(domain_func_app) => this.fallible_fold_domain_func_app(domain_func_app),
        // TODO Expr::DomainFuncApp(u, v, w, x, y, p) => this.fallible_fold_domain_func_app(u,v,w,x,y,p),
        Expr::InhaleExhale(inhale_exhale) => this.fallible_fold_inhale_exhale(inhale_exhale),
        Expr::Downcast(downcast_expr) => this.fallible_fold_downcast(downcast_expr),
        Expr::SnapApp(snap_app) => this.fallible_fold_snap_app(snap_app),
        Expr::ContainerOp(container_op) => this.fallible_fold_container_op(container_op),
        Expr::Seq(seq) => this.fallible_fold_seq(seq),
    }
}
