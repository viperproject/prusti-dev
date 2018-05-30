// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id();

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Perm {
    pub num: u32,
    pub den: u32,
}

impl Perm {
    pub fn full() -> Self {
        Perm {
            num: 1,
            den: 1
        }
    }

    pub fn none() -> Self {
        Perm {
            num: 0,
            den: 1
        }
    }
}

impl fmt::Display for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}

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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Place {
    Base(LocalVar),
    Field(Box<Place>, Field)
}

impl Place {
    pub fn access(self, field: Field) -> Self {
        Place::Field(box self, field)
    }

    pub fn parent(&self) -> Option<&Place> {
        match self {
            &Place::Base(_) => None,
            &Place::Field(ref place, _) => Some(place)
        }
    }

    pub fn base(&self) -> &LocalVar {
        match self {
            &Place::Base(ref var) => var,
            &Place::Field(ref place, _) => place.base(),
        }
    }

    pub fn is_base(&self) -> bool {
        match self {
            &Place::Base(_) => true,
            _ => false,
        }
    }

    pub fn has_proper_prefix(&self, other: &Place) -> bool {
        self != other && self.has_prefix(other)
    }

    pub fn has_prefix(&self, other: &Place) -> bool {
        if self == other {
            true
        } else {
            match self.parent() {
                Some(parent) => parent.has_prefix(other),
                None => false
            }
        }
    }

    pub fn all_proper_prefixes(&self) -> Vec<&Place> {
        match self.parent() {
            Some(parent) => parent.all_prefixes(),
            None => vec![]
        }
    }

    pub fn all_prefixes(&self) -> Vec<&Place> {
        let mut res = self.all_proper_prefixes();
        res.push(self);
        res
    }

    pub fn get_type(&self) -> &Type {
        match self {
            &Place::Base(LocalVar { ref typ, .. }) |
            &Place::Field(_, Field { ref typ, .. }) => &typ
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        match self.get_type() {
            &Type::TypedRef(ref name) => Some(name.clone()),
            _ => None
        }
    }

    pub fn replace_prefix(self, target: &Place, replacement: Place) -> Self {
        if &self == target {
            replacement
        } else {
            match self {
                Place::Field(box base, field) => Place::Field(box base.replace_prefix(target, replacement), field),
                x => x,
            }
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Place::Base(ref var) => write!(f, "{}", var),
            &Place::Field(ref place, ref field) => write!(f, "{}.{}", place, field)
        }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Place::Base(ref var) => write!(f, "{:?}", var),
            &Place::Field(ref place, ref field) => write!(f, "({:?}).{:?}", place, field)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    Comment(String),
    Label(String),
    Inhale(Expr),
    Exhale(Expr, Id),
    Assert(Expr, Id),
    /// MethodCall: method_name, args, targets
    MethodCall(String, Vec<Expr>, Vec<LocalVar>),
    Assign(Place, Expr),
    New(LocalVar, Vec<Field>),
    Fold(String, Vec<Expr>),
    Unfold(String, Vec<Expr>),
    /// Obtain: conjunction of Expr::PredicateAccessPredicate or Expr::FieldAccessPredicate
    /// They will be used by the fold/unfold algorithm
    Obtain(Expr),
}

impl Stmt {
    pub fn comment<S: ToString>(comment: S) -> Self {
        Stmt::Comment(comment.to_string())
    }

    pub fn obtain_acc(place: Place) -> Self {
        assert!(!place.is_base());
        Stmt::Obtain(
            Expr::FieldAccessPredicate(
                box place.into(),
                Perm::full(),
            )
        )
    }

    pub fn obtain_pred(place: Place) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Obtain(
            Expr::PredicateAccessPredicate(
                box Expr::PredicateAccess(
                    predicate_name,
                    vec![place.into()],
                ),
                Perm::full(),
            )
        )
    }

    pub fn fold_pred(place: Place) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Fold(
            predicate_name,
            vec![
                place.into()
            ]
        )
    }

    pub fn unfold_pred(place: Place) -> Self {
        let predicate_name = place.typed_ref_name().unwrap();
        Stmt::Unfold(
            predicate_name,
            vec![
                place.into()
            ]
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
                f,
                "{} := {}({})",
                vars.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
                name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
            ),
            Stmt::Assign(ref lhs, ref rhs) => write!(f, "{} := {}", lhs, rhs),
            Stmt::New(ref lhs, ref fields) => write!(
                f,
                "{} := new({})",
                lhs,
                fields.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", ")
            ),

            Stmt::Fold(ref pred_name, ref args) => write!(
                f,
                "fold {}({})",
                pred_name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
            ),

            Stmt::Unfold(ref pred_name, ref args) => write!(
                f,
                "unfold {}({})",
                pred_name,
                args.iter().map(|f| f.to_string()).collect::<Vec<String>>().join(", "),
            ),

            Stmt::Obtain(ref expr) => write!(f, "obtain {}", expr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Const(Const),
    Place(Place),
    Old(Box<Expr>),
    LabelledOld(Box<Expr>, String),
    MagicWand(Box<Expr>, Box<Expr>),
    /// PredicateAccess: predicate_name, args
    PredicateAccess(String, Vec<Expr>),
    PredicateAccessPredicate(Box<Expr>, Perm),
    FieldAccessPredicate(Box<Expr>, Perm),
    UnaryOp(UnaryOpKind, Box<Expr>),
    BinOp(BinOpKind, Box<Expr>, Box<Expr>),
    // Unfolding: predicate name, predicate_args, in_expr
    Unfolding(String, Vec<Expr>, Box<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Expr::Const(ref value) => write!(f, "{}", value),
            &Expr::Place(ref place) => write!(f, "{}", place),
            &Expr::BinOp(op, ref left, ref right) => write!(f, "({}) {} ({})", left, op, right),
            &Expr::UnaryOp(op, ref expr) => write!(f, "{}({})", op, expr),
            &Expr::PredicateAccessPredicate(ref expr, perm) => write!(f, "acc({}, {})", expr, perm),
            &Expr::FieldAccessPredicate(ref expr, perm) => write!(f, "acc({}, {})", expr, perm),
            &Expr::PredicateAccess(ref pred_name, ref args) => write!(
                f, "{}({})", pred_name,
                args.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
            ),
            &Expr::Old(ref expr) => write!(f, "old({})", expr),
            &Expr::LabelledOld(ref expr, ref label) => write!(f, "old[{}]({})", label, expr),
            &Expr::MagicWand(ref left, ref right) => write!(f, "({}) --* ({})", left, right),
            &Expr::Unfolding(ref pred_name, ref args, ref expr) => write!(
                f, "unfolding {}({}) in ({})",
                pred_name,
                args.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
                expr
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    EqCmp, GtCmp, GeCmp, LtCmp, LeCmp, Add, Sub, Mul, Div, Rem, And, Or, Implies
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
            &BinOpKind::Rem => write!(f, "%"),
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

    pub fn rem(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Rem, box left, box right)
    }

    pub fn and(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::And, box left, box right)
    }

    pub fn or(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Or, box left, box right)
    }

    pub fn implies(left: Expr, right: Expr) -> Self {
        Expr::BinOp(BinOpKind::Implies, box left, box right)
    }

    pub fn as_place(&mut self) -> Option<Place> {
        match self {
            Expr::Place(ref place) => Some(place.clone()),
            _ => None,
        }
    }

    pub fn unfolding(place: Place, expr: Expr) -> Self {
        Expr::Unfolding(
            place.typed_ref_name().unwrap(),
            vec![ place.into() ],
            box expr
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
