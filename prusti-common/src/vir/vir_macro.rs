macro_rules! vir_type {
    (Int) => {crate::vir::Type::Int};
    (Bool) => {crate::vir::Type::Bool};
}

macro_rules! vir_local {
    ($name: ident : $type: ident) => {
        crate::vir::LocalVar {
            name: stringify!($name).to_string(),
            typ: vir_type!($type)
        }
    }
}

macro_rules! vir {
    (# $comment: expr) => {
        crate::vir::Stmt::Comment($comment.to_string())
    };
    (label $label: expr) => {
        crate::vir::Stmt::Label($label.to_string())
    };
    (assert $exp: tt) => {
        crate::vir::Stmt::Assert(
            vir!($exp),
            crate::vir::FoldingBehaviour::Expr,
            crate::vir::Position::default())
    };
    (inhale $exp: tt) => {
        crate::vir::Stmt::Inhale(
            vir!($exp),
            crate::vir::FoldingBehaviour::Expr)
    };
    (apply $exp: tt) => {
        crate::vir::Stmt::ApplyMagicWand(
            vir!($exp),
            crate::vir::Position::default())
    };
    (obtain $exp: tt) => {
        crate::vir::Stmt::Obtain(
            vir!($exp),
            crate::vir::Position::default())
    };
    (if ($exp: tt) { $($then: tt);* } else { $($elze: tt);* }) => {
        crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![$(vir!($elze)),*])
    };
    (if ($exp: tt) { $($then: tt);* }) => {
        crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![])
    };
    (true) => {
        crate::vir::Expr::Const(
            crate::vir::Const::Bool(true),
            crate::vir::Position::default())
    };
    (false) => {
        crate::vir::Expr::Const(
            crate::vir::Const::Bool(false),
            crate::vir::Position::default())
    };
    ($lhs: tt == $rhs: tt) => {
        crate::vir::Expr::BinOp(vir::BinOpKind::Equals,
            Box::new(vir!($lhs)),
            Box::new(vir!($rhs)),
            crate::vir::Position::default())
    };
    ($head: tt && $tail: tt) => {
        crate::vir::Expr::BinOp(vir::BinOpKind::And,
            Box::new(vir!($head)),
            Box::new(vir!($tail)),
            crate::vir::Position::default())
    };
    ($head: tt || $tail: tt) => {
        crate::vir::Expr::BinOp(vir::BinOpKind::Or,
            Box::new(vir!($head)),
            Box::new(vir!($tail)),
            crate::vir::Position::default())
    };
    ($antecedent: tt ==> $consequent: tt) => {
        crate::vir::Expr::BinOp(vir::BinOpKind::Implies,
            Box::new(vir!($antecedent)),
            Box::new(vir!($consequent)),
            crate::vir::Position::default())
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        crate::vir::Expr::magic_wand(vir!($lhs), vir!($rhs), $borrow)
    };
    (forall $($name: ident : $type: ident),+ :: {$trigger: tt} $body: tt) => {
        crate::vir::Expr::ForAll(
            vec![$(vir_local!($name: $type)),+],
            vec![crate::vir::Trigger::new(vec![vir!($trigger)])],
            Box::new(vir!($body)),
            crate::vir::Position::default())
    };
    ([ $e: expr ]) => { $e.clone() };
    (( $($tokens: tt)+ )) => { vir!($($tokens)+) }
}
