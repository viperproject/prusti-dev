// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// TODO: Remove this and fix.
#![allow(deprecated)]

use std::fmt;
use std::ops::Mul;
use num_rational::Ratio;

pub use num_traits::One;
pub use num_traits::Zero;

/// The identifier of a statement. Used in error reporting.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    line: i32,
    column: i32,
    id: String
}

impl Position {
    pub fn new(line: i32, column: i32, id: String) -> Self {
        Position {
            line,
            column,
            id
        }
    }

    pub fn line(&self) -> i32 {
        self.line
    }

    pub fn column(&self) -> i32 {
        self.column
    }

    pub fn id(&self) -> String {
        self.id.to_string()
    }
}

pub type Frac = Ratio<u32>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Bool,
    //Ref, // At the moment we don't need this
    /// TypedRef: the first parameter is the name of the predicate that encodes the type
    TypedRef(String)
}

impl Type {
    pub fn is_ref(&self) -> bool {
        match self {
            //&Type::Ref |
            &Type::TypedRef(_) => true,
            _ => false
        }
    }

    pub fn name(&self) -> String {
        match self {
            &Type::Bool => "bool".to_string(),
            &Type::Int => "int".to_string(),
            &Type::TypedRef(ref pred_name) => format!("{}", pred_name),
        }
    }

    pub fn weak_eq(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Bool, Type::Bool) |
            (Type::Int, Type::Int) |
            (Type::TypedRef(_), Type::TypedRef(_)) => true,

            _ => false
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Type::Int => write!(f, "Int"),
            &Type::Bool => write!(f, "Bool"),
            //&Type::Ref => write!(f, "Ref"),
            &Type::TypedRef(ref name) => write!(f, "Ref({})", name),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct LocalVar {
    pub name: String,
    pub typ: Type
}

impl LocalVar {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        LocalVar {
            name: name.into(),
            typ
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.typ {
            Type::TypedRef(ref name) => Some(name.clone()),
            _ => None
        }
    }

    pub fn weak_eq(&self, other: &LocalVar) -> bool {
        self.name == other.name && self.typ.weak_eq(&other.typ)
    }
}

impl fmt::Display for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for LocalVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub name: String,
    pub typ: Type
}

impl Field {
    pub fn new<S: Into<String>>(name: S, typ: Type) -> Self {
        Field {
            name: name.into(),
            typ
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.typ {
            Type::TypedRef(ref name) => Some(name.clone()),
            _ => None
        }
    }

    pub fn weak_eq(&self, other: &Field) -> bool {
        self.name == other.name && self.typ.weak_eq(&other.typ)
    }
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.typ)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    Comment(String),
    Label(String),
    Inhale(Expr),
    Exhale(Expr, Position),
    Assert(Expr, Position),
    /// MethodCall: method_name, args, targets
    MethodCall(String, Vec<Expr>, Vec<LocalVar>),
    Assign(Expr, Expr, AssignKind),
    Fold(String, Vec<Expr>, Frac),
    Unfold(String, Vec<Expr>, Frac),
    /// Obtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    Obtain(Expr),
    /// WeakObtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    #[deprecated]
    WeakObtain(Expr),
    /// Havoc: used for emptying the fold/unfold state
    #[deprecated]
    Havoc,
    /// Mark a CFG point in which all current permissions are framed out
    /// They will be used by the fold/unfold algorithm
    BeginFrame,
    /// Mark a CFG point in which all the permissions of a corresponding `BeginFraming` are framed in
    /// They will be used by the fold/unfold algorithm
    EndFrame,
    /// Move permissions from a place to another.
    /// This is used to restore permissions in the fold/unfold state when a loan expires.
    TransferPerm(Expr, Expr),
    /// An `if` statement: the guard, the 'then' branch, the 'else' branch
    /// Note: this is only used to restore permissions of expiring loans, so the fold/unfold
    /// algorithms threats this statement (and statements in the branches) in a very special way.
    ExpireBorrowsIf(Expr, Vec<Stmt>, Vec<Stmt>),
    /// A statement that informs the fold/unfold that we finished restoring a DAG of expiring loans
    StopExpiringLoans,
    /// Package a Magic Wand
    /// Arguments: the magic wand, then the package statements.
    PackageMagicWand(Expr, Vec<Stmt>, Position),
    /// Apply a Magic Wand.
    /// Arguments: the magic wand.
    ApplyMagicWand(Expr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssignKind {
    /// Encodes a Rust copy.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is *not* Ref.
    Copy,
    /// Encodes a Rust move. The permissions in the rhs move to the `lhs`.
    /// This assignment can be used iff the Viper type of the `lhs` and `rhs` is Ref.
    Move,
    /// Encodes the initialization of a mutable borrow.
    /// The permissions in the `rhs` move to the `lhs`, but they can be restored when the borrow dies.
    MutableBorrow
}

impl Stmt {
    pub fn is_comment(&self) -> bool {
        match self {
            Stmt::Comment(_) => true,
            _ => false
        }
    }

    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(comment.to_string())
    }

    pub fn obtain_acc(place: Expr) -> Self {
        assert!(!place.is_local());
        Stmt::Obtain(
            Expr::FieldAccessPredicate(
                box place,
                Frac::one(),
            )
        )
    }

    pub fn obtain_pred(place: Expr) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Obtain(
            Expr::PredicateAccessPredicate(
                predicate_name,
                vec![ place ],
                Frac::one(),
            )
        )
    }

    pub fn fold_pred(place: Expr, frac: Frac) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Fold(
            predicate_name,
            vec![
                place.into()
            ],
            frac
        )
    }

    pub fn unfold_pred(place: Expr, frac: Frac) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Unfold(
            predicate_name,
            vec![ place ],
            frac
        )
    }

    pub fn package_magic_wand(lhs: Expr, rhs: Expr, stmts: Vec<Stmt>, pos: Position) -> Self {
        Stmt::PackageMagicWand(
            Expr::MagicWand(box lhs, box rhs),
            stmts,
            pos
        )
    }

    pub fn apply_magic_wand(lhs: Expr, rhs: Expr) -> Self {
        Stmt::ApplyMagicWand(
            Expr::MagicWand(box lhs, box rhs),
        )
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Stmt::Comment(ref comment) => write!(f, "// {}", comment),
            Stmt::Label(ref label) => write!(f, "label {}", label),
            Stmt::Inhale(ref expr) => write!(f, "inhale {}", expr),
            Stmt::Exhale(ref expr, _) => write!(f, "exhale {}", expr),
            Stmt::Assert(ref expr, _) => write!(f, "assert {}", expr),
            Stmt::MethodCall(ref name, ref args, ref vars) => write!(
                f, "{} := {}({})",
                vars.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
            ),
            Stmt::Assign(ref lhs, ref rhs, kind) => match kind {
                AssignKind::Move => write!(f, "{} := move {}", lhs, rhs),
                AssignKind::Copy => write!(f, "{} := copy {}", lhs, rhs),
                AssignKind::MutableBorrow => write!(f, "{} := borrow {}", lhs, rhs),
            },

            Stmt::Fold(ref pred_name, ref args, frac) => if *frac == Frac::one() {
                write!(
                    f, "fold {}({})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                )
            } else {
                write!(
                    f, "fold acc({}({}), {})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                    frac,
                )
            },

            Stmt::Unfold(ref pred_name, ref args, frac) => if *frac == Frac::one() {
                write!(
                    f, "unfold {}({})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                )
            } else {
                write!(
                    f, "unfold acc({}({}), {})",
                    pred_name,
                    args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                    frac,
                )
            },

            Stmt::Obtain(ref expr) => write!(f, "obtain {}", expr),

            Stmt::WeakObtain(ref expr) => write!(f, "weak obtain {}", expr),

            Stmt::Havoc => write!(f, "havoc"),

            Stmt::BeginFrame => write!(f, "begin frame"),

            Stmt::EndFrame => write!(f, "end frame"),

            Stmt::TransferPerm(ref lhs, ref rhs) => write!(f, "transfer perm {} --> {}", lhs, rhs),

            Stmt::ExpireBorrowsIf(ref guard, ref then_stmts, ref else_stmts) => {
                write!(f, "expire borrows if {} {{", guard)?;
                if !then_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in then_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "    \n"))?;
                }
                write!(f, "}} else {{")?;
                if !else_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in else_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "    \n"))?;
                }
                write!(f, "}}")
            }

            Stmt::StopExpiringLoans => write!(f, "stop expiring borrows"),

            Stmt::PackageMagicWand(Expr::MagicWand(ref lhs, ref rhs), ref package_stmts, _position) => {
                writeln!(f, "package {}", lhs)?;
                writeln!(f, "    --* {}", rhs)?;
                write!(f, "{{")?;
                if !package_stmts.is_empty() {
                    write!(f, "\n")?;
                }
                for stmt in package_stmts.iter() {
                    writeln!(f, "    {}", stmt.to_string().replace("\n", "    \n"))?;
                }
                write!(f, "}}")
            }

            Stmt::ApplyMagicWand(Expr::MagicWand(ref lhs, ref rhs)) => {
                writeln!(f, "apply {} --* {}", lhs, rhs)
            }

            ref x => unimplemented!("{:?}", x),
        }
    }
}


pub trait StmtFolder {
    fn fold(&mut self, e: Stmt) -> Stmt {
        match e {
            Stmt::Comment(s) => self.fold_comment(s),
            Stmt::Label(s) => self.fold_label(s),
            Stmt::Inhale(e) => self.fold_inhale(e),
            Stmt::Exhale(e, p) => self.fold_exhale(e, p),
            Stmt::Assert(e, p) => self.fold_assert(e, p),
            Stmt::MethodCall(s, ve, vv) => self.fold_method_call(s, ve, vv),
            Stmt::Assign(p, e, k) => self.fold_assign(p, e, k),
            Stmt::Fold(s, ve, frac) => self.fold_fold(s, ve, frac),
            Stmt::Unfold(s, ve, frac) => self.fold_unfold(s, ve, frac),
            Stmt::Obtain(e) => self.fold_obtain(e),
            Stmt::WeakObtain(e) => self.fold_weak_obtain(e),
            Stmt::Havoc => self.fold_havoc(),
            Stmt::BeginFrame => self.fold_begin_frame(),
            Stmt::EndFrame => self.fold_end_frame(),
            Stmt::TransferPerm(a, b) => self.fold_transfer_perm(a, b),
            Stmt::ExpireBorrowsIf(g, t, e) => self.fold_expire_borrows_if(g, t, e),
            Stmt::StopExpiringLoans => self.fold_stop_expiring_borrows(),
            Stmt::PackageMagicWand(w, s, p) => self.fold_package_magic_wand(w, s, p),
            Stmt::ApplyMagicWand(w) => self.fold_apply_magic_wand(w),
        }
    }

    fn fold_expr(&mut self, e: Expr) -> Expr {
        e
    }

    fn fold_comment(&mut self, s: String) -> Stmt {
        Stmt::Comment(s)
    }

    fn fold_label(&mut self, s: String) -> Stmt {
        Stmt::Label(s)
    }

    fn fold_inhale(&mut self, e: Expr) -> Stmt {
        Stmt::Inhale(self.fold_expr(e))
    }

    fn fold_exhale(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Exhale(self.fold_expr(e), p)
    }

    fn fold_assert(&mut self, e: Expr, p: Position) -> Stmt {
        Stmt::Assert(self.fold_expr(e), p)
    }

    fn fold_method_call(&mut self, s: String, ve: Vec<Expr>, vv: Vec<LocalVar>) -> Stmt {
        Stmt::MethodCall(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), vv)
    }

    fn fold_assign(&mut self, p: Expr, e: Expr, k: AssignKind) -> Stmt {
        Stmt::Assign(self.fold_expr(p), self.fold_expr(e), k)
    }

    fn fold_fold(&mut self, s: String, ve: Vec<Expr>, frac: Frac) -> Stmt {
        Stmt::Fold(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), frac)
    }

    fn fold_unfold(&mut self, s: String, ve: Vec<Expr>, frac: Frac) -> Stmt {
        Stmt::Unfold(s, ve.into_iter().map(|e| self.fold_expr(e)).collect(), frac)
    }

    fn fold_obtain(&mut self, e: Expr) -> Stmt {
        Stmt::Obtain(self.fold_expr(e))
    }

    fn fold_weak_obtain(&mut self, e: Expr) -> Stmt {
        Stmt::WeakObtain(self.fold_expr(e))
    }

    fn fold_havoc(&mut self) -> Stmt {
        Stmt::Havoc
    }

    fn fold_begin_frame(&mut self) -> Stmt {
        Stmt::BeginFrame
    }

    fn fold_end_frame(&mut self) -> Stmt {
        Stmt::EndFrame
    }

    fn fold_transfer_perm(&mut self, a: Expr, b: Expr) -> Stmt {
        Stmt::TransferPerm(self.fold_expr(a), self.fold_expr(b))
    }

    fn fold_expire_borrows_if(&mut self, g: Expr, t: Vec<Stmt>, e: Vec<Stmt>) -> Stmt {
        Stmt::ExpireBorrowsIf(
            self.fold_expr(g),
            t.into_iter().map(|x| self.fold(x)).collect(),
            e.into_iter().map(|x| self.fold(x)).collect()
        )
    }

    fn fold_stop_expiring_borrows(&mut self) -> Stmt {
        Stmt::StopExpiringLoans
    }

    fn fold_package_magic_wand(&mut self, w: Expr, s: Vec<Stmt>, p: Position) -> Stmt {
        Stmt::PackageMagicWand(
            self.fold_expr(w),
            s.into_iter().map(|x| self.fold(x)).collect(),
            p
        )
    }

    fn fold_apply_magic_wand(&mut self, w: Expr) -> Stmt {
        Stmt::ApplyMagicWand(
            self.fold_expr(w),
        )
    }
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// FuncApp: function_name, args, formal_args, return_type, Viper position
    FuncApp(String, Vec<Expr>, Vec<LocalVar>, Type, Position),
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
        Expr::FuncApp(ref x, ref y, ref z, ref k, ref p) => this.walk_func_app(x, y, z, k, p),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trigger(Vec<Expr>);

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
            Expr::FuncApp(ref name, ref args, ..) => write!(
                f, "{}({})",
                name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", ")
            ),
        }
    }
}

impl fmt::Display for Trigger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{{{}}}",
            self.0.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
        )
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


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    EqCmp, GtCmp, GeCmp, LtCmp, LeCmp, Add, Sub, Mul, Div, Mod, And, Or, Implies
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
            &BinOpKind::Mul => write!(f, "-"),
            &BinOpKind::Div => write!(f, "\\"),
            &BinOpKind::Mod => write!(f, "%"),
            &BinOpKind::And => write!(f, "&&"),
            &BinOpKind::Or => write!(f, "||"),
            &BinOpKind::Implies => write!(f, "==>"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    Not, Minus
}

impl fmt::Display for UnaryOpKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &UnaryOpKind::Not => write!(f, "!"),
            &UnaryOpKind::Minus => write!(f, "-"),
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
            Expr::ge_cmp(left.clone(), 0.into()),
            // positive value
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
        pub struct ExprPlaceFinder<'a> {
            sub_target: &'a Expr,
            found: bool
        }
        impl<'a> ExprWalker for ExprPlaceFinder<'a> {
            fn walk(&mut self, expr: &Expr) {
                if expr.is_place() {
                    if expr.has_prefix(self.sub_target) {
                        self.found = true;
                    }
                } else {
                    default_walk_expr(self, expr)
                }
            }
        }

        let mut finder = ExprPlaceFinder {
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

    /// Only defined for places
    pub fn get_parent(&self) -> Option<Expr> {
        debug_assert!(self.is_place());
        match self {
            &Expr::Local(_) => None,
            &Expr::Field(box ref base, _) |
            &Expr::AddrOf(box ref base, _) => Some(base.clone()),
            &Expr::LabelledOld(ref label, box ref base) => base.get_parent().map(|p| p.old(label)),
            &Expr::Unfolding(ref name, ref args, box ref base, frac) => {
                base.get_parent().map(
                    |parent| {
                        match parent {
                            // Simplify
                            Expr::Local(..) |
                            Expr::LabelledOld(..) => parent,

                            // Keep unfolding expression
                            _ => {
                                Expr::Unfolding(
                                    name.clone(),
                                    args.clone(),
                                    box parent,
                                    frac
                                )
                            }
                        }

                    }
                )
            },
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

    /// Puts the an `old[label](..)` around the expression
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

    pub fn has_old(&self) -> bool {
        self.contains_old_label()
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
            replacement: &'a Expr
        };
        impl<'a> ExprFolder for PlaceReplacer<'a> {
            fn fold(&mut self, e: Expr) -> Expr {
                if e.is_place() && e.weak_eq(self.target) {
                    self.replacement.clone()
                } else {
                    default_fold_expr(self, e)
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
        PlaceReplacer {
            target,
            replacement
        }.fold(self)
    }
}

impl Trigger {
    pub fn new(items: Vec<Expr>) -> Self {
        Trigger(items)
    }

    pub fn elements(&self) -> &Vec<Expr> {
        &self.0
    }

    pub fn replace_place(self, target: &Expr, replacement: &Expr) -> Self {
        Trigger(
            self.0.into_iter().map(|x| x.replace_place(target, replacement)).collect()
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    Bool(bool),
    Null,
    Int(i64),
    BigInt(String),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Predicate {
    pub name: String,
    pub args: Vec<LocalVar>,
    pub body: Option<Expr>,
}

impl Predicate {
    pub fn new<S: Into<String>>(name: S, args: Vec<LocalVar>, body: Option<Expr>) -> Self {
        Predicate {
            name: name.into(),
            args,
            body
        }
    }
}

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "predicate {}(", self.name)?;
        let mut first = true;
        for arg in &self.args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        match self.body {
            None => {
                writeln!(f, ");")
            },
            Some(ref body) => {
                writeln!(f, "){{")?;
                writeln!(f, "  {}", body)?;
                writeln!(f, "}}")
            }
        }
    }
}

/// A bodyless method
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BodylessMethod {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub formal_returns: Vec<LocalVar>,
}

impl fmt::Display for BodylessMethod {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "method {}(", self.name)?;
        let mut first = true;
        for arg in &self.formal_args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        write!(f, ") returns (")?;
        for arg in &self.formal_returns {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        write!(f, ");")
    }
}

/// A function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub pres: Vec<Expr>,
    pub posts: Vec<Expr>,
    pub body: Option<Expr>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "function {}(", self.name)?;
        let mut first = true;
        for arg in &self.formal_args {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", arg)?;
            first = false
        }
        writeln!(f, "): {}", self.return_type)?;
        for pre in &self.pres {
            writeln!(f, "  requires {}", pre)?;
        }
        for post in &self.posts {
            writeln!(f, "  ensures {}", post)?;
        }
        if let Some(ref body) = self.body {
            writeln!(f, "{{")?;
            writeln!(f, "\t{}", body)?;
            write!(f, "}}")?;
        }
        write!(f, "")
    }
}
