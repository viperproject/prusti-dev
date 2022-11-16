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

    fn fold_variant(&mut self, expr: Variant) -> Expr {
        let Variant {
            base,
            variant_index,
            position,
        } = expr;
        Expr::Variant(Variant {
            base: self.fold_boxed(base),
            variant_index,
            position,
        })
    }

    fn fold_field(&mut self, expr: FieldExpr) -> Expr {
        let FieldExpr {
            base,
            field,
            position,
        } = expr;
        Expr::Field(FieldExpr {
            base: self.fold_boxed(base),
            field,
            position,
        })
    }

    fn fold_addr_of(&mut self, expr: AddrOf) -> Expr {
        let AddrOf {
            base,
            addr_type,
            position,
        } = expr;
        Expr::AddrOf(AddrOf {
            base: self.fold_boxed(base),
            addr_type,
            position,
        })
    }

    fn fold_const(&mut self, const_expr: ConstExpr) -> Expr {
        Expr::Const(const_expr)
    }

    fn fold_labelled_old(&mut self, expr: LabelledOld) -> Expr {
        let LabelledOld {
            label,
            base,
            position,
        } = expr;
        Expr::LabelledOld(LabelledOld {
            label,
            base: self.fold_boxed(base),
            position,
        })
    }

    fn fold_magic_wand(&mut self, expr: MagicWand) -> Expr {
        let MagicWand {
            left,
            right,
            borrow,
            position,
        } = expr;
        Expr::MagicWand(MagicWand {
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            borrow,
            position,
        })
    }

    fn fold_predicate_access_predicate(&mut self, expr: PredicateAccessPredicate) -> Expr {
        let PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        } = expr;
        Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type,
            argument: self.fold_boxed(argument),
            permission,
            position,
        })
    }

    fn fold_field_access_predicate(&mut self, expr: FieldAccessPredicate) -> Expr {
        let FieldAccessPredicate {
            base,
            permission,
            position,
        } = expr;
        Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: self.fold_boxed(base),
            permission,
            position,
        })
    }

    fn fold_unary_op(&mut self, expr: UnaryOp) -> Expr {
        let UnaryOp {
            op_kind,
            argument,
            position,
        } = expr;
        Expr::UnaryOp(UnaryOp {
            op_kind,
            argument: self.fold_boxed(argument),
            position,
        })
    }

    fn fold_bin_op(&mut self, expr: BinOp) -> Expr {
        let BinOp {
            op_kind,
            left,
            right,
            position,
        } = expr;
        Expr::BinOp(BinOp {
            op_kind,
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            position,
        })
    }

    fn fold_unfolding(&mut self, expr: Unfolding) -> Expr {
        let Unfolding {
            predicate,
            arguments,
            base,
            permission,
            variant,
            position,
        } = expr;
        Expr::Unfolding(Unfolding {
            predicate,
            arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
            base: self.fold_boxed(base),
            permission,
            variant,
            position,
        })
    }

    fn fold_cond(&mut self, expr: Cond) -> Expr {
        let Cond {
            guard,
            then_expr,
            else_expr,
            position,
        } = expr;
        Expr::Cond(Cond {
            guard: self.fold_boxed(guard),
            then_expr: self.fold_boxed(then_expr),
            else_expr: self.fold_boxed(else_expr),
            position,
        })
    }

    fn fold_forall(&mut self, expr: ForAll) -> Expr {
        let ForAll {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Expr::ForAll(ForAll {
            variables,
            triggers: triggers
                .iter()
                .map(|set| {
                    Trigger::new(
                        set.elements()
                            .iter()
                            .cloned()
                            .map(|expr| self.fold(expr))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_exists(&mut self, expr: Exists) -> Expr {
        let Exists {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Expr::Exists(Exists {
            variables,
            triggers: triggers
                .iter()
                .map(|set| {
                    Trigger::new(
                        set.elements()
                            .iter()
                            .cloned()
                            .map(|expr| self.fold(expr))
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_let_expr(&mut self, expr: LetExpr) -> Expr {
        let LetExpr {
            variable,
            def,
            body,
            position,
        } = expr;
        Expr::LetExpr(LetExpr {
            variable,
            def: self.fold_boxed(def),
            body: self.fold_boxed(body),
            position,
        })
    }

    fn fold_func_app(&mut self, expr: FuncApp) -> Expr {
        let FuncApp {
            function_name,
            type_arguments,
            arguments,
            formal_arguments,
            return_type,
            position,
        } = expr;
        Expr::FuncApp(FuncApp {
            function_name,
            type_arguments,
            arguments: arguments.into_iter().map(|e| self.fold(e)).collect(),
            formal_arguments,
            return_type,
            position,
        })
    }

    fn fold_domain_func_app(&mut self, expr: DomainFuncApp) -> Expr {
        let DomainFuncApp {
            domain_function,
            arguments,
            position,
        } = expr;
        Expr::DomainFuncApp(DomainFuncApp {
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
    fn fold_inhale_exhale(&mut self, expr: InhaleExhale) -> Expr {
        let InhaleExhale {
            inhale_expr,
            exhale_expr,
            position,
        } = expr;
        Expr::InhaleExhale(InhaleExhale {
            inhale_expr: self.fold_boxed(inhale_expr),
            exhale_expr: self.fold_boxed(exhale_expr),
            position,
        })
    }

    fn fold_downcast(&mut self, expr: DowncastExpr) -> Expr {
        let DowncastExpr {
            base,
            enum_place,
            field,
        } = expr;
        Expr::Downcast(DowncastExpr {
            base: self.fold_boxed(base),
            enum_place: self.fold_boxed(enum_place),
            field,
        })
    }

    fn fold_snap_app(&mut self, expr: SnapApp) -> Expr {
        let SnapApp { base, position } = expr;
        Expr::SnapApp(SnapApp {
            base: self.fold_boxed(base),
            position,
        })
    }

    fn fold_container_op(&mut self, expr: ContainerOp) -> Expr {
        let ContainerOp {
            op_kind,
            left,
            right,
            position,
        } = expr;
        Expr::ContainerOp(ContainerOp {
            op_kind,
            left: self.fold_boxed(left),
            right: self.fold_boxed(right),
            position,
        })
    }

    fn fold_seq(&mut self, expr: Seq) -> Expr {
        let Seq {
            typ,
            elements,
            position,
        } = expr;
        Expr::Seq(Seq {
            typ,
            elements: elements.into_iter().map(|e| self.fold(e)).collect(),
            position,
        })
    }

    fn fold_map(&mut self, expr: Map) -> Expr {
        let Map {
            typ,
            elements,
            position,
        } = expr;
        Expr::Map(Map {
            typ,
            elements: elements.into_iter().map(|e| self.fold(e)).collect(),
            position,
        })
    }

    fn fold_cast(&mut self, expr: Cast) -> Expr {
        Expr::Cast(Cast {
            kind: expr.kind,
            base: self.fold_boxed(expr.base),
            position: expr.position,
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
        Expr::MagicWand(magic_wand) => this.fold_magic_wand(magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => {
            this.fold_predicate_access_predicate(predicate_access_predicate)
        }
        Expr::FieldAccessPredicate(field_access_predicate) => {
            this.fold_field_access_predicate(field_access_predicate)
        }
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
        Expr::Map(map) => this.fold_map(map),
        Expr::Cast(cast) => this.fold_cast(cast),
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

    fn walk_local(&mut self, expr: &Local) {
        let Local { variable, .. } = expr;
        self.walk_local_var(variable);
    }
    fn walk_variant(&mut self, expr: &Variant) {
        let Variant {
            base,
            variant_index,
            ..
        } = expr;
        self.walk(base);
        self.walk_type(&variant_index.typ);
    }
    fn walk_field(&mut self, expr: &FieldExpr) {
        let FieldExpr { base, field, .. } = expr;
        self.walk(base);
        self.walk_type(&field.typ);
    }
    fn walk_addr_of(&mut self, expr: &AddrOf) {
        let AddrOf {
            base, addr_type, ..
        } = expr;
        self.walk(base);
        self.walk_type(addr_type);
    }
    fn walk_const(&mut self, _const_expr: &ConstExpr) {}
    fn walk_labelled_old(&mut self, expr: &LabelledOld) {
        let LabelledOld { base, .. } = expr;
        self.walk(base);
    }
    fn walk_magic_wand(&mut self, expr: &MagicWand) {
        let MagicWand { left, right, .. } = expr;
        self.walk(left);
        self.walk(right);
    }
    fn walk_predicate_access_predicate(&mut self, expr: &PredicateAccessPredicate) {
        let PredicateAccessPredicate { argument, .. } = expr;
        self.walk(argument);
    }
    fn walk_field_access_predicate(&mut self, expr: &FieldAccessPredicate) {
        let FieldAccessPredicate { base, .. } = expr;
        self.walk(base);
    }
    fn walk_unary_op(&mut self, expr: &UnaryOp) {
        let UnaryOp { argument, .. } = expr;
        self.walk(argument)
    }
    fn walk_bin_op(&mut self, expr: &BinOp) {
        let BinOp { left, right, .. } = expr;
        self.walk(left);
        self.walk(right);
    }
    fn walk_unfolding(&mut self, expr: &Unfolding) {
        let Unfolding {
            arguments, base, ..
        } = expr;
        for arg in arguments {
            self.walk(arg);
        }
        self.walk(base);
    }
    fn walk_cond(&mut self, expr: &Cond) {
        let Cond {
            guard,
            then_expr,
            else_expr,
            ..
        } = expr;
        self.walk(guard);
        self.walk(then_expr);
        self.walk(else_expr);
    }
    fn walk_forall(&mut self, expr: &ForAll) {
        let ForAll {
            variables,
            triggers,
            body,
            ..
        } = expr;
        for set in triggers {
            for expr in set.elements() {
                self.walk(expr);
            }
        }
        for var in variables {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_exists(&mut self, expr: &Exists) {
        let Exists {
            variables,
            triggers,
            body,
            ..
        } = expr;
        for set in triggers {
            for expr in set.elements() {
                self.walk(expr);
            }
        }
        for var in variables {
            self.walk_local_var(var);
        }
        self.walk(body);
    }
    fn walk_let_expr(&mut self, expr: &LetExpr) {
        let LetExpr {
            variable,
            def,
            body,
            ..
        } = expr;
        self.walk_local_var(variable);
        self.walk(def);
        self.walk(body);
    }
    fn walk_func_app(&mut self, expr: &FuncApp) {
        let FuncApp {
            arguments,
            formal_arguments,
            return_type,
            ..
        } = expr;
        for arg in arguments {
            self.walk(arg)
        }
        for arg in formal_arguments {
            self.walk_local_var(arg);
        }
        self.walk_type(return_type);
    }
    fn walk_domain_func_app(&mut self, expr: &DomainFuncApp) {
        let DomainFuncApp {
            domain_function,
            arguments,
            ..
        } = expr;
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
    fn walk_inhale_exhale(&mut self, expr: &InhaleExhale) {
        let InhaleExhale {
            inhale_expr,
            exhale_expr,
            ..
        } = expr;
        self.walk(inhale_expr);
        self.walk(exhale_expr);
    }

    fn walk_downcast(&mut self, expr: &DowncastExpr) {
        let DowncastExpr {
            base, enum_place, ..
        } = expr;
        self.walk(base);
        self.walk(enum_place);
    }
    fn walk_snap_app(&mut self, expr: &SnapApp) {
        let SnapApp { base, .. } = expr;
        self.walk(base);
    }

    fn walk_container_op(&mut self, expr: &ContainerOp) {
        let ContainerOp { left, right, .. } = expr;
        self.walk(left);
        self.walk(right);
    }

    fn walk_seq(&mut self, expr: &Seq) {
        let Seq { typ, elements, .. } = expr;
        for elem in elements {
            self.walk(elem);
        }
        self.walk_type(typ);
    }

    fn walk_map(&mut self, expr: &Map) {
        let Map { typ, elements, .. } = expr;
        for elem in elements {
            self.walk(elem);
        }
        self.walk_type(typ);
    }

    fn walk_cast(&mut self, expr: &Cast) {
        let Cast { base, .. } = expr;
        self.walk(base);
    }
}

pub fn default_walk_expr<T: ExprWalker>(this: &mut T, e: &Expr) {
    match e {
        Expr::Local(local) => this.walk_local(local),
        Expr::Variant(variant) => this.walk_variant(variant),
        Expr::Field(field_expr) => this.walk_field(field_expr),
        Expr::AddrOf(addr_of) => this.walk_addr_of(addr_of),
        Expr::Const(const_expr) => this.walk_const(const_expr),
        Expr::LabelledOld(labelled_old) => this.walk_labelled_old(labelled_old),
        Expr::MagicWand(magic_wand) => this.walk_magic_wand(magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => {
            this.walk_predicate_access_predicate(predicate_access_predicate)
        }
        Expr::FieldAccessPredicate(field_access_predicate) => {
            this.walk_field_access_predicate(field_access_predicate)
        }
        Expr::UnaryOp(unary_op) => this.walk_unary_op(unary_op),
        Expr::BinOp(bin_op) => this.walk_bin_op(bin_op),
        Expr::Unfolding(unfolding) => this.walk_unfolding(unfolding),
        Expr::Cond(cond) => this.walk_cond(cond),
        Expr::ForAll(forall) => this.walk_forall(forall),
        Expr::Exists(exists) => this.walk_exists(exists),
        Expr::LetExpr(let_expr) => this.walk_let_expr(let_expr),
        Expr::FuncApp(func_app) => this.walk_func_app(func_app),
        Expr::DomainFuncApp(domain_func_app) => this.walk_domain_func_app(domain_func_app),
        // TODO Expr::DomainFuncApp(ref u, ref v, ref w, ref x, ref y,ref p) => this.walk_domain_func_app(u, v, w, x,y,p),
        Expr::InhaleExhale(inhale_exhale) => this.walk_inhale_exhale(inhale_exhale),
        Expr::Downcast(downcast_expr) => this.walk_downcast(downcast_expr),
        Expr::SnapApp(snap_app) => this.walk_snap_app(snap_app),
        Expr::ContainerOp(container_op) => this.walk_container_op(container_op),
        Expr::Seq(seq) => this.walk_seq(seq),
        Expr::Map(map) => this.walk_map(map),
        Expr::Cast(cast) => this.walk_cast(cast),
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

    fn fallible_fold_variant(&mut self, expr: Variant) -> Result<Expr, Self::Error> {
        let Variant {
            base,
            variant_index,
            position,
        } = expr;
        Ok(Expr::Variant(Variant {
            base: self.fallible_fold_boxed(base)?,
            variant_index,
            position,
        }))
    }

    fn fallible_fold_field(&mut self, expr: FieldExpr) -> Result<Expr, Self::Error> {
        let FieldExpr {
            base,
            field,
            position,
        } = expr;
        Ok(Expr::Field(FieldExpr {
            base: self.fallible_fold_boxed(base)?,
            field,
            position,
        }))
    }

    fn fallible_fold_addr_of(&mut self, expr: AddrOf) -> Result<Expr, Self::Error> {
        let AddrOf {
            base,
            addr_type,
            position,
        } = expr;
        Ok(Expr::AddrOf(AddrOf {
            base: self.fallible_fold_boxed(base)?,
            addr_type,
            position,
        }))
    }

    fn fallible_fold_const(&mut self, const_expr: ConstExpr) -> Result<Expr, Self::Error> {
        Ok(Expr::Const(const_expr))
    }

    fn fallible_fold_labelled_old(&mut self, expr: LabelledOld) -> Result<Expr, Self::Error> {
        let LabelledOld {
            label,
            base,
            position,
        } = expr;
        Ok(Expr::LabelledOld(LabelledOld {
            label,
            base: self.fallible_fold_boxed(base)?,
            position,
        }))
    }

    fn fallible_fold_magic_wand(&mut self, expr: MagicWand) -> Result<Expr, Self::Error> {
        let MagicWand {
            left,
            right,
            borrow,
            position,
        } = expr;
        Ok(Expr::MagicWand(MagicWand {
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            borrow,
            position,
        }))
    }

    fn fallible_fold_predicate_access_predicate(
        &mut self,
        expr: PredicateAccessPredicate,
    ) -> Result<Expr, Self::Error> {
        let PredicateAccessPredicate {
            predicate_type,
            argument,
            permission,
            position,
        } = expr;
        Ok(Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type,
            argument: self.fallible_fold_boxed(argument)?,
            permission,
            position,
        }))
    }

    fn fallible_fold_field_access_predicate(
        &mut self,
        expr: FieldAccessPredicate,
    ) -> Result<Expr, Self::Error> {
        let FieldAccessPredicate {
            base,
            permission,
            position,
        } = expr;
        Ok(Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: self.fallible_fold_boxed(base)?,
            permission,
            position,
        }))
    }

    fn fallible_fold_unary_op(&mut self, expr: UnaryOp) -> Result<Expr, Self::Error> {
        let UnaryOp {
            op_kind,
            argument,
            position,
        } = expr;
        Ok(Expr::UnaryOp(UnaryOp {
            op_kind,
            argument: self.fallible_fold_boxed(argument)?,
            position,
        }))
    }

    fn fallible_fold_bin_op(&mut self, expr: BinOp) -> Result<Expr, Self::Error> {
        let BinOp {
            op_kind,
            left,
            right,
            position,
        } = expr;
        Ok(Expr::BinOp(BinOp {
            op_kind,
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            position,
        }))
    }

    fn fallible_fold_unfolding(&mut self, expr: Unfolding) -> Result<Expr, Self::Error> {
        let Unfolding {
            predicate,
            arguments,
            base,
            permission,
            variant,
            position,
        } = expr;
        Ok(Expr::Unfolding(Unfolding {
            predicate,
            arguments: arguments
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            base: self.fallible_fold_boxed(base)?,
            permission,
            variant,
            position,
        }))
    }

    fn fallible_fold_cond(&mut self, expr: Cond) -> Result<Expr, Self::Error> {
        let Cond {
            guard,
            then_expr,
            else_expr,
            position,
        } = expr;
        Ok(Expr::Cond(Cond {
            guard: self.fallible_fold_boxed(guard)?,
            then_expr: self.fallible_fold_boxed(then_expr)?,
            else_expr: self.fallible_fold_boxed(else_expr)?,
            position,
        }))
    }

    fn fallible_fold_forall(&mut self, expr: ForAll) -> Result<Expr, Self::Error> {
        let ForAll {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Ok(Expr::ForAll(ForAll {
            variables,
            triggers: triggers
                .iter()
                .map(|set| {
                    Ok(Trigger::new(
                        set.elements()
                            .iter()
                            .cloned()
                            .map(|expr| self.fallible_fold(expr))
                            .collect::<Result<Vec<_>, _>>()?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_exists(&mut self, expr: Exists) -> Result<Expr, Self::Error> {
        let Exists {
            variables,
            triggers,
            body,
            position,
        } = expr;
        Ok(Expr::Exists(Exists {
            variables,
            triggers: triggers
                .iter()
                .map(|set| {
                    Ok(Trigger::new(
                        set.elements()
                            .iter()
                            .cloned()
                            .map(|expr| self.fallible_fold(expr))
                            .collect::<Result<Vec<_>, _>>()?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_let_expr(&mut self, expr: LetExpr) -> Result<Expr, Self::Error> {
        let LetExpr {
            variable,
            def,
            body,
            position,
        } = expr;
        Ok(Expr::LetExpr(LetExpr {
            variable,
            def: self.fallible_fold_boxed(def)?,
            body: self.fallible_fold_boxed(body)?,
            position,
        }))
    }

    fn fallible_fold_func_app(&mut self, expr: FuncApp) -> Result<Expr, Self::Error> {
        let FuncApp {
            function_name,
            type_arguments,
            arguments,
            formal_arguments,
            return_type,
            position,
        } = expr;
        Ok(Expr::FuncApp(FuncApp {
            function_name,
            type_arguments,
            arguments: arguments
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<Vec<_>, Self::Error>>()?,
            formal_arguments,
            return_type,
            position,
        }))
    }

    fn fallible_fold_domain_func_app(&mut self, expr: DomainFuncApp) -> Result<Expr, Self::Error> {
        let DomainFuncApp {
            domain_function,
            arguments,
            position,
        } = expr;
        Ok(Expr::DomainFuncApp(DomainFuncApp {
            domain_function,
            arguments: arguments
                .into_iter()
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
    fn fallible_fold_inhale_exhale(&mut self, expr: InhaleExhale) -> Result<Expr, Self::Error> {
        let InhaleExhale {
            inhale_expr,
            exhale_expr,
            position,
        } = expr;
        Ok(Expr::InhaleExhale(InhaleExhale {
            inhale_expr: self.fallible_fold_boxed(inhale_expr)?,
            exhale_expr: self.fallible_fold_boxed(exhale_expr)?,
            position,
        }))
    }

    fn fallible_fold_downcast(&mut self, expr: DowncastExpr) -> Result<Expr, Self::Error> {
        let DowncastExpr {
            base,
            enum_place,
            field,
        } = expr;
        Ok(Expr::Downcast(DowncastExpr {
            base: self.fallible_fold_boxed(base)?,
            enum_place: self.fallible_fold_boxed(enum_place)?,
            field,
        }))
    }

    fn fallible_fold_snap_app(&mut self, expr: SnapApp) -> Result<Expr, Self::Error> {
        let SnapApp { base, position } = expr;
        Ok(Expr::SnapApp(SnapApp {
            base: self.fallible_fold_boxed(base)?,
            position,
        }))
    }

    fn fallible_fold_container_op(&mut self, expr: ContainerOp) -> Result<Expr, Self::Error> {
        let ContainerOp {
            op_kind,
            left,
            right,
            position,
        } = expr;
        Ok(Expr::ContainerOp(ContainerOp {
            op_kind,
            left: self.fallible_fold_boxed(left)?,
            right: self.fallible_fold_boxed(right)?,
            position,
        }))
    }

    fn fallible_fold_seq(&mut self, expr: Seq) -> Result<Expr, Self::Error> {
        let Seq {
            typ,
            elements,
            position,
        } = expr;
        Ok(Expr::Seq(Seq {
            typ,
            elements: elements
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            position,
        }))
    }

    fn fallible_fold_map(&mut self, expr: Map) -> Result<Expr, Self::Error> {
        let Map {
            typ,
            elements,
            position,
        } = expr;
        Ok(Expr::Map(Map {
            typ,
            elements: elements
                .into_iter()
                .map(|e| self.fallible_fold(e))
                .collect::<Result<_, _>>()?,
            position,
        }))
    }

    fn fallible_fold_cast(&mut self, expr: Cast) -> Result<Expr, Self::Error> {
        let Cast {
            kind,
            base,
            position,
        } = expr;
        Ok(Expr::Cast(Cast {
            kind,
            base: self.fallible_fold_boxed(base)?,
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
        Expr::PredicateAccessPredicate(predicate_access_predicate) => {
            this.fallible_fold_predicate_access_predicate(predicate_access_predicate)
        }
        Expr::FieldAccessPredicate(field_access_predicate) => {
            this.fallible_fold_field_access_predicate(field_access_predicate)
        }
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
        Expr::Map(map) => this.fallible_fold_map(map),
        Expr::Cast(cast) => this.fallible_fold_cast(cast),
    }
}

pub trait FallibleExprWalker: Sized {
    type Error;

    fn fallible_walk(&mut self, expr: &Expr) -> Result<(), Self::Error> {
        default_fallible_walk_expr(self, expr)
    }

    fn fallible_walk_type(&mut self, _typ: &Type) -> Result<(), Self::Error> {
        Ok(())
    }
    fn fallible_walk_local_var(&mut self, var: &LocalVar) -> Result<(), Self::Error> {
        self.fallible_walk_type(&var.typ)
    }

    fn fallible_walk_local(&mut self, expr: &Local) -> Result<(), Self::Error> {
        let Local { variable, .. } = expr;
        self.fallible_walk_local_var(variable)
    }
    fn fallible_walk_variant(&mut self, expr: &Variant) -> Result<(), Self::Error> {
        let Variant {
            base,
            variant_index,
            ..
        } = expr;
        self.fallible_walk(base)?;
        self.fallible_walk_type(&variant_index.typ)
    }
    fn fallible_walk_field(&mut self, expr: &FieldExpr) -> Result<(), Self::Error> {
        let FieldExpr { base, field, .. } = expr;
        self.fallible_walk(base)?;
        self.fallible_walk_type(&field.typ)
    }
    fn fallible_walk_addr_of(&mut self, expr: &AddrOf) -> Result<(), Self::Error> {
        let AddrOf {
            base, addr_type, ..
        } = expr;
        self.fallible_walk(base)?;
        self.fallible_walk_type(addr_type)
    }
    fn fallible_walk_const(&mut self, _const_expr: &ConstExpr) -> Result<(), Self::Error> {
        Ok(())
    }
    fn fallible_walk_labelled_old(&mut self, expr: &LabelledOld) -> Result<(), Self::Error> {
        let LabelledOld { base, .. } = expr;
        self.fallible_walk(base)
    }
    fn fallible_walk_magic_wand(&mut self, expr: &MagicWand) -> Result<(), Self::Error> {
        let MagicWand { left, right, .. } = expr;
        self.fallible_walk(left)?;
        self.fallible_walk(right)?;
        Ok(())
    }
    fn fallible_walk_predicate_access_predicate(
        &mut self,
        expr: &PredicateAccessPredicate,
    ) -> Result<(), Self::Error> {
        let PredicateAccessPredicate { argument, .. } = expr;
        self.fallible_walk(argument)
    }
    fn fallible_walk_field_access_predicate(
        &mut self,
        expr: &FieldAccessPredicate,
    ) -> Result<(), Self::Error> {
        let FieldAccessPredicate { base, .. } = expr;
        self.fallible_walk(base)
    }
    fn fallible_walk_unary_op(&mut self, expr: &UnaryOp) -> Result<(), Self::Error> {
        let UnaryOp { argument, .. } = expr;
        self.fallible_walk(argument)
    }
    fn fallible_walk_bin_op(&mut self, expr: &BinOp) -> Result<(), Self::Error> {
        let BinOp { left, right, .. } = expr;
        self.fallible_walk(left)?;
        self.fallible_walk(right)?;
        Ok(())
    }
    fn fallible_walk_unfolding(&mut self, expr: &Unfolding) -> Result<(), Self::Error> {
        let Unfolding {
            arguments, base, ..
        } = expr;
        for arg in arguments {
            self.fallible_walk(arg)?;
        }
        self.fallible_walk(base)
    }
    fn fallible_walk_cond(&mut self, expr: &Cond) -> Result<(), Self::Error> {
        let Cond {
            guard,
            then_expr,
            else_expr,
            ..
        } = expr;
        self.fallible_walk(guard)?;
        self.fallible_walk(then_expr)?;
        self.fallible_walk(else_expr)?;
        Ok(())
    }
    fn fallible_walk_forall(&mut self, expr: &ForAll) -> Result<(), Self::Error> {
        let ForAll {
            variables,
            triggers,
            body,
            ..
        } = expr;
        for var in variables {
            self.fallible_walk_local_var(var)?;
        }
        for set in triggers {
            for expr in set.elements() {
                self.fallible_walk(expr)?;
            }
        }
        self.fallible_walk(body)
    }
    fn fallible_walk_exists(&mut self, expr: &Exists) -> Result<(), Self::Error> {
        let Exists {
            variables,
            triggers,
            body,
            ..
        } = expr;
        for var in variables {
            self.fallible_walk_local_var(var)?;
        }
        for set in triggers {
            for expr in set.elements() {
                self.fallible_walk(expr)?;
            }
        }
        self.fallible_walk(body)
    }
    fn fallible_walk_let_expr(&mut self, expr: &LetExpr) -> Result<(), Self::Error> {
        let LetExpr {
            variable,
            def,
            body,
            ..
        } = expr;
        self.fallible_walk_local_var(variable)?;
        self.fallible_walk(def)?;
        self.fallible_walk(body)?;
        Ok(())
    }
    fn fallible_walk_func_app(&mut self, expr: &FuncApp) -> Result<(), Self::Error> {
        let FuncApp {
            arguments,
            formal_arguments,
            return_type,
            ..
        } = expr;
        for arg in arguments {
            self.fallible_walk(arg)?;
        }
        for arg in formal_arguments {
            self.fallible_walk_local_var(arg)?;
        }
        self.fallible_walk_type(return_type)
    }
    fn fallible_walk_domain_func_app(&mut self, expr: &DomainFuncApp) -> Result<(), Self::Error> {
        let DomainFuncApp {
            domain_function,
            arguments,
            ..
        } = expr;
        for arg in arguments {
            self.fallible_walk(arg)?;
        }
        for arg in &domain_function.formal_args {
            self.fallible_walk_local_var(arg)?;
        }
        self.fallible_walk_type(&domain_function.return_type)
    }
    /* TODO
    fn fallible_walk_domain_func_app-> Result<(), Self::Error> (
        &mut self,
        _function_name: &String,
        args: &Vec<Expr>,
        formal_args: &Vec<LocalVar>,
        _return_type: &Type,
        _domain_name: &String,
        _pos: &Position) {
        for arg in args {
            self.fallible_walk(arg)
        }
        for arg in formal_args {
            self.fallible_walk_local_var(arg)
        }
    }
    */
    fn fallible_walk_inhale_exhale(&mut self, expr: &InhaleExhale) -> Result<(), Self::Error> {
        let InhaleExhale {
            inhale_expr,
            exhale_expr,
            ..
        } = expr;
        self.fallible_walk(inhale_expr)?;
        self.fallible_walk(exhale_expr)?;
        Ok(())
    }

    fn fallible_walk_downcast(&mut self, expr: &DowncastExpr) -> Result<(), Self::Error> {
        let DowncastExpr {
            base, enum_place, ..
        } = expr;
        self.fallible_walk(base)?;
        self.fallible_walk(enum_place)?;
        Ok(())
    }

    fn fallible_walk_snap_app(&mut self, expr: &SnapApp) -> Result<(), Self::Error> {
        let SnapApp { base, .. } = expr;
        self.fallible_walk(base)
    }

    fn fallible_walk_container_op(&mut self, expr: &ContainerOp) -> Result<(), Self::Error> {
        let ContainerOp { left, right, .. } = expr;
        self.fallible_walk(left)?;
        self.fallible_walk(right)?;
        Ok(())
    }

    fn fallible_walk_seq(&mut self, expr: &Seq) -> Result<(), Self::Error> {
        let Seq { typ, elements, .. } = expr;
        for elem in elements {
            self.fallible_walk(elem)?;
        }
        self.fallible_walk_type(typ)
    }

    fn fallible_walk_map(&mut self, expr: &Map) -> Result<(), Self::Error> {
        let Map { typ, elements, .. } = expr;
        for elem in elements {
            self.fallible_walk(elem)?;
        }
        self.fallible_walk_type(typ)
    }

    fn fallible_walk_cast(&mut self, expr: &Cast) -> Result<(), Self::Error> {
        let Cast { base, .. } = expr;
        self.fallible_walk(base)
    }
}

pub fn default_fallible_walk_expr<U, T: FallibleExprWalker<Error = U>>(
    this: &mut T,
    e: &Expr,
) -> Result<(), U> {
    match e {
        Expr::Local(local) => this.fallible_walk_local(local),
        Expr::Variant(variant) => this.fallible_walk_variant(variant),
        Expr::Field(field_expr) => this.fallible_walk_field(field_expr),
        Expr::AddrOf(addr_of) => this.fallible_walk_addr_of(addr_of),
        Expr::Const(const_expr) => this.fallible_walk_const(const_expr),
        Expr::LabelledOld(labelled_old) => this.fallible_walk_labelled_old(labelled_old),
        Expr::MagicWand(magic_wand) => this.fallible_walk_magic_wand(magic_wand),
        Expr::PredicateAccessPredicate(predicate_access_predicate) => {
            this.fallible_walk_predicate_access_predicate(predicate_access_predicate)
        }
        Expr::FieldAccessPredicate(field_access_predicate) => {
            this.fallible_walk_field_access_predicate(field_access_predicate)
        }
        Expr::UnaryOp(unary_op) => this.fallible_walk_unary_op(unary_op),
        Expr::BinOp(bin_op) => this.fallible_walk_bin_op(bin_op),
        Expr::Unfolding(unfolding) => this.fallible_walk_unfolding(unfolding),
        Expr::Cond(cond) => this.fallible_walk_cond(cond),
        Expr::ForAll(forall) => this.fallible_walk_forall(forall),
        Expr::Exists(exists) => this.fallible_walk_exists(exists),
        Expr::LetExpr(let_expr) => this.fallible_walk_let_expr(let_expr),
        Expr::FuncApp(func_app) => this.fallible_walk_func_app(func_app),
        Expr::DomainFuncApp(domain_func_app) => this.fallible_walk_domain_func_app(domain_func_app),
        // TODO Expr::DomainFuncApp(ref u, ref v, ref w, ref x, ref y,ref p) => this.fallible_walk_domain_func_app(u, v, w, x,y,p),
        Expr::InhaleExhale(inhale_exhale) => this.fallible_walk_inhale_exhale(inhale_exhale),
        Expr::Downcast(downcast_expr) => this.fallible_walk_downcast(downcast_expr),
        Expr::SnapApp(snap_app) => this.fallible_walk_snap_app(snap_app),
        Expr::ContainerOp(container_op) => this.fallible_walk_container_op(container_op),
        Expr::Seq(seq) => this.fallible_walk_seq(seq),
        Expr::Map(map) => this.fallible_walk_map(map),
        Expr::Cast(cast) => this.fallible_walk_cast(cast),
    }
}
