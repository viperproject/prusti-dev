// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use std::mem;
use encoder::vir::ast::*;
use std::ops::Mul;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum Expr {
    /// A local var
    Local(LocalVar),
    /// A field access
    Field(Box<Expr>, Field),
    /// The inverse of a `val_ref` field access
    AddrOf(Box<Expr>, Type),
    LabelledOld(String, Box<Expr>),
    Const(Const),
    MagicWand(Box<Expr>, Box<Expr>),
    /// PredicateAccessPredicate: predicate_name, args, frac
    PredicateAccessPredicate(String, Vec<Expr>, Frac),
    FieldAccessPredicate(Box<Expr>, Frac),
    UnaryOp(UnaryOpKind, Box<Expr>),
    BinOp(BinOpKind, Box<Expr>, Box<Expr>),
    // Unfolding: predicate name, predicate_args, in_expr
    Unfolding(String, Vec<Expr>, Box<Expr>, Frac),
    // Cond: guard, then_expr, else_expr
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    // ForAll: variables, triggers, body
    ForAll(Vec<LocalVar>, Vec<Trigger>, Box<Expr>),
    // let variable == (expr) in body
    LetExpr(LocalVar, Box<Expr>, Box<Expr>),
    /// FuncApp: function_name, args, formal_args, return_type, Viper position
    FuncApp(String, Vec<Expr>, Vec<LocalVar>, Type, Position),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    Not, Minus
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    EqCmp, GtCmp, GeCmp, LtCmp, LeCmp, Add, Sub, Mul, Div, Mod, And, Or, Implies
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    Bool(bool),
    Null,
    Int(i64),
    BigInt(String),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::Local(ref v) => write!(f, "{}", v),
            Expr::Field(ref base, ref field) => write!(f, "{}.{}", base, field),
            Expr::AddrOf(ref base, _) => write!(f, "&({})", base),
            Expr::Const(ref value) => write!(f, "{}", value),
            Expr::BinOp(op, ref left, ref right) => write!(f, "({}) {} ({})", left, op, right),
            Expr::UnaryOp(op, ref expr) => write!(f, "{}({})", op, expr),
            Expr::PredicateAccessPredicate(ref pred_name, ref args, perm) => write!(
                f, "acc({}({}), {})",
                pred_name,
                args.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
                perm
            ),
            Expr::FieldAccessPredicate(ref expr, perm) => write!(f, "acc({}, {})", expr, perm),
            Expr::LabelledOld(ref label, ref expr) => write!(f, "old[{}]({})", label, expr),
            Expr::MagicWand(ref left, ref right) => write!(f, "({}) --* ({})", left, right),
            Expr::Unfolding(ref pred_name, ref args, ref expr, frac) => if *frac == Frac::one() {
                write!(
                    f, "(unfolding {}({}) in {})",
                    pred_name,
                    args.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
                    expr
                )
            } else {
                write!(
                    f, "(unfolding acc({}({}), {}) in {})",
                    pred_name,
                    args.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
                    frac,
                    expr
                )
            },
            Expr::Cond(ref guard, ref left, ref right) => write!(f, "({})?({}):({})", guard, left, right),
            Expr::ForAll(ref vars, ref triggers, ref body) => write!(
                f, "forall {} {} :: {}",
                vars.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", "),
                triggers.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
                body.to_string()
            ),
            Expr::LetExpr(ref var, ref expr, ref body) => write!(
                f, "(let {:?} == ({}) in {})",
                var,
                expr.to_string(),
                body.to_string()
            ),
            Expr::FuncApp(ref name, ref args, ..) => write!(
                f, "{}({})",
                name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", ")
            ),
        }
    }
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &UnaryOpKind::Not => write!(f, "!"),
            &UnaryOpKind::Minus => write!(f, "-"),
        }
    }
}

impl fmt::Display for BinOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &BinOpKind::EqCmp => write!(f, "=="),
            &BinOpKind::GtCmp => write!(f, ">"),
            &BinOpKind::GeCmp => write!(f, ">="),
            &BinOpKind::LtCmp => write!(f, "<"),
            &BinOpKind::LeCmp => write!(f, "<="),
            &BinOpKind::Add => write!(f, "+"),
            &BinOpKind::Sub => write!(f, "-"),
            &BinOpKind::Mul => write!(f, "*"),
            &BinOpKind::Div => write!(f, "\\"),
            &BinOpKind::Mod => write!(f, "%"),
            &BinOpKind::And => write!(f, "&&"),
            &BinOpKind::Or => write!(f, "||"),
            &BinOpKind::Implies => write!(f, "==>"),
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Const::Bool(val) => write!(f, "{}", val),
            &Const::Null => write!(f, "null"),
            &Const::Int(val) => write!(f, "{}", val),
            &Const::BigInt(ref val) => write!(f, "{}", val),
        }
    }
}

impl Expr {
    pub fn pred_permission(place: Expr, frac: Frac) -> Option<Self> {
        place.typed_ref_name().map( |pred_name|
            Expr::PredicateAccessPredicate(
                pred_name,
                vec![ place ],
                frac,
            )
        )
    }

    pub fn acc_permission(place: Expr, frac: Frac) -> Self {
        Expr::FieldAccessPredicate(
            box place,
            frac
        )
    }

    pub fn labelled_old(label: &str, expr: Expr) -> Self {
        Expr::LabelledOld(label.to_string(), box expr)
    }

    pub fn not(expr: Expr) -> Self {
        Expr::UnaryOp(UnaryOpKind::Not, box expr)
    }

    pub fn minus(expr: Expr) -> Self {
        Expr::UnaryOp(UnaryOpKind::Minus, box expr)
    }

    pub fn gt_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::GtCmp, box left, box right)
    }

    pub fn ge_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::GeCmp, box left, box right)
    }

    pub fn lt_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::LtCmp, box left, box right)
    }

    pub fn le_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::LeCmp, box left, box right)
    }

    pub fn eq_cmp(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::EqCmp, box left, box right)
    }

    pub fn ne_cmp(left: Expr, right: Expr) -> Self {
        Expr::not(Expr::eq_cmp(left, right))
    }

    pub fn add(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Add, box left, box right)
    }

    pub fn sub(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Sub, box left, box right)
    }

    pub fn mul(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Mul, box left, box right)
    }

    pub fn div(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Div, box left, box right)
    }

    pub fn modulo(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Mod, box left, box right)
    }

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
                Expr::eq_cmp(
                    Expr::modulo(left.clone(), right.clone()),
                    0.into()
                )
            ),
            // positive value or left % right == 0
            Expr::modulo(left.clone(), right.clone()),
            // negative value
            Expr::sub(Expr::modulo(left, right), abs_right),
        )
    }

    pub fn and(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::And, box left, box right)
    }

    pub fn or(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Or, box left, box right)
    }

    pub fn xor(left: Expr, right: Expr) -> Self {
        Expr::not(Expr::eq_cmp(left, right))
    }

    pub fn implies(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Implies, box left, box right)
    }

    pub fn let_expr(variable: LocalVar, expr: Expr, body: Expr) -> Self {
        Expr::LetExpr(variable, box expr, box body)
    }

    pub fn forall(vars: Vec<LocalVar>, triggers: Vec<Trigger>, body: Expr) -> Self {
        Expr::ForAll(vars, triggers, box body)
    }

    pub fn ite(guard: Expr, left: Expr, right: Expr) -> Self {
        Expr::Cond(box guard, box left, box right)
    }

    pub fn unfolding(place: Expr, expr: Expr, frac: Frac) -> Self {
        Expr::Unfolding(
            place.typed_ref_name().unwrap(),
            vec![ place ],
            box expr,
            frac
        )
    }

    pub fn func_app(name: String, args: Vec<Expr>, internal_args: Vec<LocalVar>, return_type: Type, pos: Position) -> Self {
        Expr::FuncApp(
            name,
            args,
            internal_args,
            return_type,
            pos
        )
    }

    pub fn find(&self, sub_target: &Expr) -> bool {
        pub struct ExprFinder<'a> {
            sub_target: &'a Expr,
            found: bool
        }
        impl<'a> ExprWalker for ExprFinder<'a> {
            fn walk(&mut self, expr: &Expr) {
                if expr == self.sub_target || (expr.is_place() && expr.weak_eq(self.sub_target)) {
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

    pub fn explode_place(&self) -> (Expr, Vec<Field>) {
        match self {
            Expr::Field(ref base, ref field) => {
                let (base_base, mut fields) = base.explode_place();
                fields.push(field.clone());
                (base_base, fields)
            }
            _ => (self.clone(), vec![])
        }
    }

    // Methods from Place

    pub fn local(local: LocalVar) -> Self {
        Expr::Local(local)
    }

    pub fn field(self, field: Field) -> Self {
        Expr::Field(box self, field)
    }

    pub fn addr_of(self) -> Self {
        let type_name = self.get_type().name();
        Expr::AddrOf(box self, Type::TypedRef(type_name))
    }

    pub fn is_place(&self) -> bool {
        match self {
            &Expr::Local(_) => true,
            &Expr::Field(ref base, _) |
            &Expr::AddrOf(ref base, _) |
            &Expr::LabelledOld(_, ref base) |
            &Expr::Unfolding(_, _, ref base, _) => base.is_place(),
            _ => false
        }
    }

    pub fn is_simple_place(&self) -> bool {
        match self {
            &Expr::Local(_) => true,
            &Expr::Field(ref base, _) => base.is_simple_place(),
            _ => false
        }
    }

    /// Only defined for places
    pub fn get_parent(&self) -> Option<Expr> {
        debug_assert!(self.is_place());
        match self {
            &Expr::Local(_) => None,
            &Expr::Field(box ref base, _) |
            &Expr::AddrOf(box ref base, _) => Some(base.clone()),
            &Expr::LabelledOld(_, _) => None,
            &Expr::Unfolding(ref name, ref args, box ref base, frac) => None,
            ref x => panic!("{}", x),
        }
    }

    pub fn map_parent<F>(self, f: F) -> Expr where F: Fn(Expr) -> Expr {
        match self {
            Expr::Field(box base, field) => Expr::Field(box f(base), field),
            Expr::AddrOf(box base, ty) => Expr::AddrOf(box f(base), ty),
            Expr::LabelledOld(label, box base) => Expr::LabelledOld(label, box f(base)),
            Expr::Unfolding(name, args, box base, frac) => Expr::Unfolding(name, args, box f(base), frac),
            _ => self,
        }
    }

    pub fn is_local(&self) -> bool {
        match self {
            &Expr::Local(..) => true,
            _ => false,
        }
    }

    pub fn is_field(&self) -> bool {
        match self {
            &Expr::Field(..) => true,
            _ => false,
        }
    }

    pub fn is_addr_of(&self) -> bool {
        match self {
            &Expr::AddrOf(..) => true,
            _ => false,
        }
    }

    pub fn is_unfolding(&self) -> bool {
        match self {
            &Expr::Unfolding(..) => true,
            _ => false,
        }
    }

    /// Puts an `old[label](..)` around the expression
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
            },
            Expr::LabelledOld(..) => {
                /*
                debug!(
                    "Trying to put an old expression 'old[{}](..)' around {}, which already has a label",
                    label,
                    self
                );
                */
                self
            },
            _ => Expr::LabelledOld(label.to_string(), box self)
        }
    }

    /// Puts the place into an `old[label](..)` expression, if the label is not `None`
    pub fn maybe_old<S: fmt::Display + ToString>(self, label: Option<S>) -> Self {
        match label {
            None => self,
            Some(label) => self.old(label),
        }
    }

    pub fn contains_old_label(&self) -> bool {
        struct OldLabelFinder {
            found: bool
        }
        impl ExprWalker for OldLabelFinder {
            fn walk_labelled_old(&mut self, x: &str, y: &Expr) {
                self.found = true;
            }
        }
        let mut walker = OldLabelFinder{
            found: false
        };
        walker.walk(self);
        walker.found
    }

    pub fn is_old(&self) -> bool {
        self.get_label().is_some()
    }

    pub fn is_curr(&self) -> bool {
        !self.is_old()
    }

    pub fn get_place(&self) -> Option<&Expr> {
        match self {
            Expr::PredicateAccessPredicate(_, ref args, _) => Some(&args[0]),
            Expr::FieldAccessPredicate(box ref arg, _) => Some(arg),
            _ => None,
        }
    }

    pub fn is_pure(&self) -> bool {
        struct PurityFinder {
            non_pure: bool
        }
        impl ExprWalker for PurityFinder {
            fn walk_predicate_access_predicate(&mut self,x: &str, y: &Vec<Expr>, z: Frac) {
                self.non_pure = true;
            }
            fn walk_field_access_predicate(&mut self, x: &Expr, y: Frac) {
                self.non_pure = true;
            }
        }
        let mut walker = PurityFinder{
            non_pure: false
        };
        walker.walk(self);
        !walker.non_pure
    }

    /// Only defined for places
    pub fn get_base(&self) -> LocalVar {
        debug_assert!(self.is_place());
        match self {
            &Expr::Local(ref var) => var.clone(),
            &Expr::LabelledOld(_, ref base) |
            &Expr::Unfolding(_, _, ref base, _) => base.get_base(),
            _ => self.get_parent().unwrap().get_base(),
        }
    }

    pub fn get_label(&self) -> Option<&String> {
        match self {
            &Expr::LabelledOld(ref label, _) => Some(label),
            _ => None,
        }
    }

    /// Place equality after type elision
    pub fn weak_eq(&self, other: &Expr) -> bool {
        debug_assert!(self.is_place());
        debug_assert!(other.is_place());
        match (self, other) {
            (
                Expr::Local(ref self_var),
                Expr::Local(ref other_var)
            ) => self_var.weak_eq(other_var),
            (
                Expr::Field(box ref self_base, ref self_field),
                Expr::Field(box ref other_base, ref other_field)
            ) => self_field.weak_eq(other_field) && self_base.weak_eq(other_base),
            (
                Expr::AddrOf(box ref self_base, ref self_typ),
                Expr::AddrOf(box ref other_base, ref other_typ)
            ) => self_typ.weak_eq(other_typ) && self_base.weak_eq(other_base),
            (
                Expr::LabelledOld(ref self_label, box ref self_base),
                Expr::LabelledOld(ref other_label, box ref other_base)
            ) => self_label == other_label && self_base.weak_eq(other_base),
            (
                Expr::Unfolding(ref self_name, ref self_args, box ref self_base, self_frac),
                Expr::Unfolding(ref other_name, ref other_args, box ref other_base, other_frac)
            ) => self_name == other_name && self_frac == other_frac &&
                self_args[0].weak_eq(&other_args[0]) && self_base.weak_eq(other_base),
            _ => false
        }
    }

    pub fn has_proper_prefix(&self, other: &Expr) -> bool {
        debug_assert!(self.is_place());
        debug_assert!(other.is_place());
        !self.weak_eq(other) && self.has_prefix(other)
    }

    pub fn has_prefix(&self, other: &Expr) -> bool {
        debug_assert!(self.is_place());
        debug_assert!(other.is_place());
        if self.weak_eq(other) {
            true
        } else {
            match self.get_parent() {
                Some(parent) => parent.has_prefix(other),
                None => false
            }
        }
    }

    pub fn all_proper_prefixes(&self) -> Vec<Expr> {
        debug_assert!(self.is_place());
        match self.get_parent() {
            Some(parent) => parent.all_prefixes(),
            None => vec![]
        }
    }

    // Returns all prefixes, from the shortest to the longest
    pub fn all_prefixes(&self) -> Vec<Expr> {
        debug_assert!(self.is_place());
        let mut res = self.all_proper_prefixes();
        res.push(self.clone());
        res
    }

    pub fn get_type(&self) -> &Type {
        debug_assert!(self.is_place());
        match self {
            &Expr::Local(LocalVar { ref typ, .. }) |
            &Expr::Field(_, Field { ref typ, .. }) |
            &Expr::AddrOf(_, ref typ) => &typ,
            &Expr::LabelledOld(_, box ref base) |
            &Expr::Unfolding(_, _, box ref base, _) => base.get_type(),
            _ => panic!()
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.get_type() {
            &Type::TypedRef(ref name) => Some(name.clone()),
            _ => None
        }
    }

    pub fn map_labels<F>(self, f: F) -> Self where F: Fn(String) -> Option<String> {
        struct OldLabelReplacer<T: Fn(String) -> Option<String>> {
            f: T
        };
        impl<T: Fn(String) -> Option<String>> ExprFolder for OldLabelReplacer<T> {
            fn fold_labelled_old(&mut self, label: String, base: Box<Expr>) -> Expr {
                match (self.f)(label) {
                    Some(new_label) => base.old(new_label),
                    None => *base
                }
            }
        }
        OldLabelReplacer{
            f
        }.fold(self)
    }

    pub fn replace_place(self, target: &Expr, replacement: &Expr) -> Self {
        debug_assert!(target.is_place());
        //assert_eq!(target.get_type(), replacement.get_type());
        if replacement.is_place() {
            assert!(
                target.get_type().weak_eq(&replacement.get_type()),
                "Cannot substitute '{}' with '{}', because they have incompatible types '{}' and '{}'",
                target,
                replacement,
                target.get_type(),
                replacement.get_type()
            );
        }
        struct PlaceReplacer<'a>{
            target: &'a Expr,
            replacement: &'a Expr,
            // FIXME: the following fields serve a grotesque hack.
            //  Purpose:  Generics. When a less-generic function-under-test desugars specs from
            //            a more-generic function, the vir::Expr contains Local's with __TYPARAM__s,
            //            but Field's with the function-under-test's concrete types. The purpose is
            //            the to "fix" the (Viper) predicates of the fields, i.e. replace those
            //            typarams with local (more) concrete types.
            //            THIS IS FRAGILE!
            typaram_substs: Option<typaram::Substs>,
            subst: bool,
        };
        impl<'a> PlaceReplacer<'a> {
        }
        impl<'a> ExprFolder for PlaceReplacer<'a> {
            fn fold(&mut self, e: Expr) -> Expr {
                if e.is_place() && e.weak_eq(self.target) {
                    self.subst = true;
                    self.replacement.clone()
                } else {
                    match default_fold_expr(self, e) {
                        Expr::Field(expr, mut field) => {
                            if let Some(ts) = &self.typaram_substs {
                                if self.subst && field.typ.is_ref() {
                                    let inner1 = field.typ.name();
                                    let inner2 = ts.apply(&inner1);
                                    debug!("replacing:\n{}\n{}\n========", &inner1, &inner2);
                                    field = Field::new(field.name, Type::TypedRef(inner2));
                                }
                            }
                            Expr::Field(expr, field)
                        }
                        x => {
                            self.subst = false;
                            x
                        },
                    }
                }
            }

            fn fold_forall(&mut self, vars: Vec<LocalVar>, triggers: Vec<Trigger>, body: Box<Expr>) -> Expr {
                if vars.contains(&self.target.get_base()) {
                    // Do nothing
                    Expr::ForAll(vars, triggers, body)
                } else {
                    Expr::ForAll(
                        vars,
                        triggers.into_iter().map(|x| x.replace_place(self.target, self.replacement)).collect(),
                        self.fold_boxed(body)
                    )
                }
            }
        }
        let typaram_substs = match (&target, &replacement) {
            (Expr::Local(tv), Expr::Local(rv)) => {
                if tv.typ.is_ref() && rv.typ.is_ref() {
                    debug!("learning:\n{}\n{}\n=======", &target.local_type(), replacement.local_type());
                    Some(typaram::Substs::learn(&target.local_type(), &replacement.local_type()))
                } else {
                    None
                }
            }
            _ => None
        };
        PlaceReplacer {
            target,
            replacement,
            typaram_substs,
            subst: false,
        }.fold(self)
    }

    /// Replaces expressions like `old[l5](old[l5](_9.val_ref).foo.bar)`
    /// into `old[l5](_9.val_ref.foo.bar)`
    pub fn remove_redundant_old(self) -> Self {
        struct RedundantOldRemover {
            current_label: Option<String>,
        };
        impl ExprFolder for RedundantOldRemover {
            fn fold_labelled_old(&mut self, label: String, base: Box<Expr>) -> Expr {
                let old_current_label = mem::replace(
                    &mut self.current_label,
                    Some(label.clone()));
                let new_base = default_fold_expr(self, *base);
                let new_expr = if Some(label.clone()) == old_current_label {
                    new_base
                } else {
                    new_base.old(label)
                };
                self.current_label = old_current_label;
                new_expr
            }
        }
        RedundantOldRemover {
            current_label: None,
        }.fold(self)
    }

    /// Leaves a conjunction of `acc(..)` expressions
    pub fn filter_perm_conjunction(self) -> Self {
        struct PermConjunctionFilter();
        impl ExprFolder for PermConjunctionFilter {
            fn fold(&mut self, e: Expr) -> Expr {
                match e {
                    f @ Expr::PredicateAccessPredicate(..) => f,
                    f @ Expr::FieldAccessPredicate(..) => f,
                    Expr::BinOp(BinOpKind::And, y, z) => self.fold_bin_op(BinOpKind::And, y, z),

                    Expr::BinOp(..) |
                    Expr::MagicWand(..) |
                    Expr::Unfolding(..) |
                    Expr::Cond(..) |
                    Expr::UnaryOp(..) |
                    Expr::Const(..) |
                    Expr::Local(..) |
                    Expr::Field(..) |
                    Expr::AddrOf(..) |
                    Expr::LabelledOld(..) |
                    Expr::ForAll(..) |
                    Expr::LetExpr(..) |
                    Expr::FuncApp(..) => true.into(),
                }
            }
        }
        PermConjunctionFilter().fold(self)
    }

    /// Apply the closure to all places in the expression.
    pub fn fold_places<F>(self, f: F) -> Expr
        where
            F: Fn(Expr) -> Expr
    {
        struct PlaceFolder<F>
            where
                F: Fn(Expr) -> Expr
        {
            f: F,
        };
        impl<F> ExprFolder for PlaceFolder<F>
            where
                F: Fn(Expr) -> Expr
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
        PlaceFolder {
            f
        }.fold(self)
    }

    pub fn local_type(&self) -> String {
        match &self {
            Expr::Local(localvar) => match &localvar.typ {
                Type::TypedRef(str) => str.clone(),
                _ => panic!("expected Type::TypedRef"),
            }
            _ => panic!("expected Expr::Local"),
        }
    }
}

impl Const {
    pub fn is_num(&self) -> bool {
        match self {
            &Const::Bool(..) |
            &Const::Null => false,

            &Const::Int(..) |
            &Const::BigInt(..) => true,
        }
    }
}

pub trait ExprFolder : Sized {
    fn fold(&mut self, e: Expr) -> Expr {
        default_fold_expr(self, e)
    }

    fn fold_boxed(&mut self, e: Box<Expr>) -> Box<Expr> {
        box self.fold(*e)
    }

    fn fold_local(&mut self, v: LocalVar) -> Expr {
        Expr::Local(v)
    }
    fn fold_field(&mut self, e: Box<Expr>, f: Field) -> Expr {
        Expr::Field(self.fold_boxed(e), f)
    }
    fn fold_addr_of(&mut self, e: Box<Expr>, t: Type) -> Expr {
        Expr::AddrOf(self.fold_boxed(e), t)
    }
    fn fold_const(&mut self, x: Const) -> Expr {
        Expr::Const(x)
    }
    fn fold_labelled_old(&mut self, x: String, y: Box<Expr>) -> Expr {
        Expr::LabelledOld(x, self.fold_boxed(y))
    }
    fn fold_magic_wand(&mut self, x: Box<Expr>, y: Box<Expr>) -> Expr {
        Expr::MagicWand(self.fold_boxed(x), self.fold_boxed(y))
    }
    fn fold_predicate_access_predicate(&mut self, x: String, y: Vec<Expr>, z: Frac) -> Expr {
        Expr::PredicateAccessPredicate(x, y.into_iter().map(|e| self.fold(e)).collect(), z)
    }
    fn fold_field_access_predicate(&mut self, x: Box<Expr>, y: Frac) -> Expr {
        Expr::FieldAccessPredicate(self.fold_boxed(x), y)
    }
    fn fold_unary_op(&mut self, x: UnaryOpKind, y: Box<Expr>) -> Expr {
        Expr::UnaryOp(x, self.fold_boxed(y))
    }
    fn fold_bin_op(&mut self, x: BinOpKind, y: Box<Expr>, z: Box<Expr>) -> Expr {
        Expr::BinOp(x, self.fold_boxed(y), self.fold_boxed(z))
    }
    fn fold_unfolding(&mut self, x: String, y: Vec<Expr>, z: Box<Expr>, frac: Frac) -> Expr {
        Expr::Unfolding(x, y.into_iter().map(|e| self.fold(e)).collect(), self.fold_boxed(z), frac)
    }
    fn fold_cond(&mut self, x: Box<Expr>, y: Box<Expr>, z: Box<Expr>) -> Expr {
        Expr::Cond(self.fold_boxed(x), self.fold_boxed(y), self.fold_boxed(z))
    }
    fn fold_forall(&mut self, x: Vec<LocalVar>, y: Vec<Trigger>, z: Box<Expr>) -> Expr {
        Expr::ForAll(x, y, self.fold_boxed(z))
    }
    fn fold_let_expr(&mut self, x: LocalVar, y: Box<Expr>, z: Box<Expr>) -> Expr {
        Expr::LetExpr(x, self.fold_boxed(y), self.fold_boxed(z))
    }
    fn fold_func_app(&mut self, x: String, y: Vec<Expr>, z: Vec<LocalVar>, k: Type, p: Position) -> Expr {
        Expr::FuncApp(x, y.into_iter().map(|e| self.fold(e)).collect(), z, k, p)
    }
}

pub fn default_fold_expr<T: ExprFolder>(this: &mut T, e: Expr) -> Expr {
    match e {
        Expr::Local(v) => this.fold_local(v),
        Expr::Field(e, f) => this.fold_field(e, f),
        Expr::AddrOf(e, t) => this.fold_addr_of(e, t),
        Expr::Const(x) => this.fold_const(x),
        Expr::LabelledOld(x, y) => this.fold_labelled_old(x, y),
        Expr::MagicWand(x, y) => this.fold_magic_wand(x, y),
        Expr::PredicateAccessPredicate(x, y, z) => this.fold_predicate_access_predicate(x, y, z),
        Expr::FieldAccessPredicate(x, y) => this.fold_field_access_predicate(x, y),
        Expr::UnaryOp(x, y) => this.fold_unary_op(x, y),
        Expr::BinOp(x, y, z) => this.fold_bin_op(x, y, z),
        Expr::Unfolding(x, y, z, frac) => this.fold_unfolding(x, y, z, frac),
        Expr::Cond(x, y, z) => this.fold_cond(x, y, z),
        Expr::ForAll(x, y, z) => this.fold_forall(x, y, z),
        Expr::LetExpr(x, y, z) => this.fold_let_expr(x, y, z),
        Expr::FuncApp(x, y, z, k, p) => this.fold_func_app(x, y, z, k, p),
    }
}

pub trait ExprWalker : Sized {
    fn walk(&mut self, e: &Expr) {
        default_walk_expr(self, e);
    }

    fn walk_local(&mut self, x: &LocalVar) {}
    fn walk_field(&mut self, e: &Expr, f: &Field) {
        self.walk(e);
    }
    fn walk_addr_of(&mut self, e: &Expr, t: &Type) {
        self.walk(e);
    }
    fn walk_const(&mut self, x: &Const) {}
    fn walk_old(&mut self, x: &Expr) {
        self.walk(x);
    }
    fn walk_labelled_old(&mut self, x: &str, y: &Expr) {
        self.walk(y);
    }
    fn walk_magic_wand(&mut self, x: &Expr, y: &Expr) {
        self.walk(x);
        self.walk(y);
    }
    fn walk_predicate_access_predicate(&mut self,x: &str, y: &Vec<Expr>, z: Frac) {
        for e in y {
            self.walk(e);
        }
    }
    fn walk_field_access_predicate(&mut self, x: &Expr, y: Frac) {
        self.walk(x)
    }
    fn walk_unary_op(&mut self, x: UnaryOpKind, y: &Expr) {
        self.walk(y)
    }
    fn walk_bin_op(&mut self, x: BinOpKind, y: &Expr, z: &Expr) {
        self.walk(y);
        self.walk(z);
    }
    fn walk_unfolding(&mut self, x: &str, y: &Vec<Expr>, z: &Expr, frac: Frac) {
        for e in y {
            self.walk(e);
        }
        self.walk(z);
    }
    fn walk_cond(&mut self, x: &Expr, y: &Expr, z: &Expr) {
        self.walk(x);
        self.walk(y);
        self.walk(z);
    }
    fn walk_forall(&mut self, x: &Vec<LocalVar>, y: &Vec<Trigger>, z: &Expr) {
        self.walk(z);
    }
    fn walk_let_expr(&mut self, x: &LocalVar, y: &Expr, z: &Expr) {
        self.walk(y);
        self.walk(z);
    }
    fn walk_func_app(&mut self, x: &str, y: &Vec<Expr>, z: &Vec<LocalVar>, k: &Type, p: &Position) {
        for e in y {
            self.walk(e)
        }
    }
}

pub fn default_walk_expr<T: ExprWalker>(this: &mut T, e: &Expr) {
    match *e {
        Expr::Local(ref v) => this.walk_local(v),
        Expr::Field(ref e, ref f) => this.walk_field(e, f),
        Expr::AddrOf(ref e, ref t) => this.walk_addr_of(e, t),
        Expr::Const(ref x) => this.walk_const(x),
        Expr::LabelledOld(ref x, ref y) => this.walk_labelled_old(x, y),
        Expr::MagicWand(ref x, ref y) => this.walk_magic_wand(x, y),
        Expr::PredicateAccessPredicate(ref x, ref y, z) => this.walk_predicate_access_predicate(x, y, z),
        Expr::FieldAccessPredicate(ref x, y) => this.walk_field_access_predicate(x, y),
        Expr::UnaryOp(x, ref y) => this.walk_unary_op(x, y),
        Expr::BinOp(x, ref y, ref z) => this.walk_bin_op(x, y, z),
        Expr::Unfolding(ref x, ref y, ref z, frac) => this.walk_unfolding(x, y, z, frac),
        Expr::Cond(ref x, ref y, ref z) => this.walk_cond(x, y, z),
        Expr::ForAll(ref x, ref y, ref z) => this.walk_forall(x, y, z),
        Expr::LetExpr(ref x, ref y, ref z) => this.walk_let_expr(x, y, z),
        Expr::FuncApp(ref x, ref y, ref z, ref k, ref p) => this.walk_func_app(x, y, z, k, p),
    }
}

impl <'a> Mul<&'a Frac> for Box<Expr> {
    type Output = Box<Expr>;

    fn mul(self, frac: &'a Frac) -> Box<Expr> {
        Box::new(*self * frac)
    }
}

impl <'a> Mul<&'a Frac> for Expr {
    type Output = Expr;

    fn mul(self, frac: &'a Frac) -> Expr {
        match self {
            Expr::PredicateAccessPredicate(x, y, z) => Expr::PredicateAccessPredicate(x, y, z * frac),
            Expr::FieldAccessPredicate(x, y) => Expr::FieldAccessPredicate(x, y * frac),
            Expr::UnaryOp(x, y) => Expr::UnaryOp(x, y * frac),
            Expr::BinOp(x, y, z) => Expr::BinOp(x, y * frac, z * frac),
            Expr::Cond(x, y, z) => Expr::Cond(x, y * frac, z * frac),
            _ => self
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
        T: Iterator<Item = Expr>
{
    fn conjoin(&mut self) -> Expr {
        if let Some(init) = self.next() {
            self.fold(init, |acc, conjunct| Expr::and(acc, conjunct))
        } else {
            true.into()
        }
    }

    fn disjoin(&mut self) -> Expr {
        if let Some(init) = self.next() {
            self.fold(init, |acc, conjunct| Expr::or(acc, conjunct))
        } else {
            false.into()
        }
    }
}
