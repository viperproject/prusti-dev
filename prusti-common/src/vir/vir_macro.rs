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
        crate::vir::Stmt::comment($comment)
    };
    (label $label: expr) => {
        crate::vir::Stmt::label($label)
    };
    (assert $exp: tt) => {
        crate::vir::Stmt::Assert(
            vir!($exp),
            FoldingBehaviour::Expr,
            Position::default())
    };
    (inhale $exp: tt) => {
        crate::vir::Stmt::Inhale(
            vir!($exp),
            FoldingBehaviour::Expr)
    };
    (apply $exp: tt) => {
        crate::vir::Stmt::ApplyMagicWand(
            vir!($exp),
            Position::default())
    };
    (obtain $exp: tt) => {
        crate::vir::Stmt::Obtain(
            vir!($exp),
            Position::default())
    };
    (if ($exp: tt) { $($then: tt);* } else { $($elze: tt);* }) => {
        crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![$(vir!($elze)),*])
    };
    (if ($exp: tt) { $($then: tt);* }) => {
        crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![])
    };
    (true) => {
        crate::vir::Expr::Const(
            Const::Bool(true),
            Position::default())
    };
    (false) => {
        crate::vir::Expr::Const(
            Const::Bool(false),
            Position::default())
    };
    ($lhs: tt == $rhs: tt) => {
        crate::vir::Expr::eq_cmp(vir!($lhs), vir!($rhs))
    };
    ($head: tt && $tail: tt) => {
        crate::vir::Expr::and(vir!($head), vir!($tail))
    };
    ($head: tt || $tail: tt) => {
        crate::vir::Expr::or(vir!($head), vir!($tail))
    };
    ($antecedent: tt ==> $consequent: tt) => {
        crate::vir::Expr::implies(vir!($antecedent), vir!($consequent))
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        crate::vir::Expr::magic_wand(vir!($lhs), vir!($rhs), $borrow)
    };

    (forall $($name: ident : $type: ident),+ :: {$trigger: tt} $body: tt) => {
        crate::vir::Expr::forall(
            vec![$(vir_local!($name: $type)),+],
            vec![Trigger::new(vec![vir!($trigger)])],
            vir!($body),
        )
    };
    ([ $e: expr ]) => { $e.clone() };
    (( $($tokens: tt)+ )) => { vir!($($tokens)+) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vir::*;

    #[test]
    fn forall() {
        let expected = Expr::ForAll(
            vec![vir_local!(i: Int), vir_local!(j: Int)],
            vec![Trigger::new(vec![vir!{ true }])],
            Box::new(vir!{ true }),
            Position::default());

        let actual = vir!{ forall i: Int, j: Int :: {true} true };

        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_passthrough() {
        let expr = vir!{ assert true };

        assert_eq!(expr, vir!{ [expr] });
        assert_eq!(expr, vir!{ ( [expr] ) });
    }
}
