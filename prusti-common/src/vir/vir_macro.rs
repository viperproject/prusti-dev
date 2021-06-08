#[macro_export]
macro_rules! vir_type {
    (Int) => {$crate::vir::Type::Int};
    (Bool) => {$crate::vir::Type::Bool};
    ({$ty:expr}) => { $ty }
}

#[macro_export]
macro_rules! vir_local {
    ($name:ident : $type:tt) => {
        $crate::vir::LocalVar {
            name: stringify!($name).to_string(),
            typ: $crate::vir_type!($type)
        }
    }
}

#[macro_export]
macro_rules! vir {
    (# $comment: expr) => {
        $crate::vir::Stmt::comment($comment)
    };
    (label $label: expr) => {
        $crate::vir::Stmt::label($label)
    };
    (assert $exp: tt) => {
        $crate::vir::Stmt::Assert(
            vir!($exp),
            $crate::vir::Position::default())
    };
    (inhale $exp: tt) => {
        $crate::vir::Stmt::Inhale(vir!($exp))
    };
    (exhale $exp: tt) => {
        $crate::vir::Stmt::Exhale(
            vir!($exp),
            $crate::vir::Position::default())
    };
    (apply $exp: tt) => {
        $crate::vir::Stmt::ApplyMagicWand(
            vir!($exp),
            $crate::vir::Position::default())
    };
    (obtain $exp: tt) => {
        $crate::vir::Stmt::Obtain(
            vir!($exp),
            $crate::vir::Position::default())
    };
    (if ($exp: tt) { $($then: tt);* } else { $($elze: tt);* }) => {
        $crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![$(vir!($elze)),*])
    };
    (if ($exp: tt) { $($then: tt);* }) => {
        $crate::vir::Stmt::If(vir!($exp), vec![$(vir!($then)),*], vec![])
    };
    (true) => {
        $crate::vir::Expr::Const(
            $crate::vir::Const::Bool(true),
            $crate::vir::Position::default())
    };
    (false) => {
        $crate::vir::Expr::Const(
            $crate::vir::Const::Bool(false),
            $crate::vir::Position::default())
    };

    ($lhs: tt == $rhs: tt) => {
        $crate::vir::Expr::eq_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt != $rhs: tt) => {
        $crate::vir::Expr::ne_cmp(vir!($lhs), vir!($rhs))
    };
    ($head: tt && $tail: tt) => {
        $crate::vir::Expr::and(vir!($head), vir!($tail))
    };
    ($head: tt || $tail: tt) => {
        $crate::vir::Expr::or(vir!($head), vir!($tail))
    };
    ($lhs: tt > $rhs: tt) => {
        $crate::vir::Expr::gt_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt >= $rhs: tt) => {
        $crate::vir::Expr::ge_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt < $rhs: tt) => {
        $crate::vir::Expr::lt_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt <= $rhs: tt) => {
        $crate::vir::Expr::le_cmp(vir!($lhs), vir!($rhs))
    };

    ($lhs: tt + $rhs: tt) => {
        $crate::vir::Expr::add(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt - $rhs: tt) => {
        $crate::vir::Expr::sub(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt * $rhs: tt) => {
        $crate::vir::Expr::mul(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt / $rhs: tt) => {
        $crate::vir::Expr::div(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt % $rhs: tt) => {
        $crate::vir::Expr::modulo(vir!($lhs), vir!($rhs))
    };

    ($antecedent: tt ==> $consequent: tt) => {
        $crate::vir::Expr::implies(vir!($antecedent), vir!($consequent))
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        $crate::vir::Expr::magic_wand(vir!($lhs), vir!($rhs), $borrow)
    };

    (forall $($name: ident : $type: tt),+ :: {$($triggers: tt),*} $body: tt) => {
        $crate::vir::Expr::forall(
            vec![$($crate::vir_local!($name: $type)),+],
            vec![$($crate::vir::Trigger::new(vec![vir!($triggers)])),*],
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
            vec![Trigger::new(vec![vir!{ true }]), Trigger::new(vec![vir!{ false }])],
            Box::new(vir!{ true }),
            Position::default());

        let actual = vir!{ forall i: Int, j: Int :: {true, false} true };

        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_passthrough() {
        let expr = vir!{ assert true };

        assert_eq!(expr, vir!{ [expr] });
        assert_eq!(expr, vir!{ ( [expr] ) });
    }
}
