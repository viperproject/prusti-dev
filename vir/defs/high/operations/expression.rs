use super::{
    super::ast::{
        expression::{
            visitors::{
                default_fold_expression, default_walk_expression, ExpressionFolder,
                ExpressionWalker,
            },
            *,
        },
        position::Position,
    },
    ty::Typed,
};

impl Expression {
    pub fn is_place(&self) -> bool {
        match self {
            Expression::Local(_) => true,
            Expression::Variant(Variant { base, .. })
            | Expression::Field(Field { base, .. })
            | Expression::Deref(Deref { base, .. })
            | Expression::AddrOf(AddrOf { base, .. })
            | Expression::LabelledOld(LabelledOld { base, .. }) => base.is_place(),
            _ => false,
        }
    }
    pub fn replace_place(self, target: &Expression, replacement: &Expression) -> Self {
        debug_assert!(target.is_place());
        assert_eq!(target.get_type(), replacement.get_type());
        struct PlaceReplacer<'a> {
            target: &'a Expression,
            replacement: &'a Expression,
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_place() && &expression == self.target {
                    self.replacement.clone()
                } else {
                    default_fold_expression(self, expression)
                }
            }
        }
        let mut replacer = PlaceReplacer {
            target,
            replacement,
        };
        replacer.fold_expression(self)
    }
    /// Simplify `Deref(AddrOf(P))` to `P`.
    pub fn simplify_addr_of(self) -> Self {
        struct Simplifier;
        impl ExpressionFolder for Simplifier {
            fn fold_field(
                &mut self,
                Field {
                    base: receiver,
                    field,
                    position,
                }: Field,
            ) -> Expression {
                if let Expression::AddrOf(AddrOf { base, .. }) = *receiver {
                    *base
                } else {
                    Expression::field(self.fold_expression(*receiver), field, position)
                }
            }
        }
        Simplifier.fold_expression(self)
    }
    pub fn find(&self, sub_target: &Expression) -> bool {
        pub struct ExprFinder<'a> {
            sub_target: &'a Expression,
            found: bool,
        }
        impl<'a> ExpressionWalker for ExprFinder<'a> {
            fn walk_expression(&mut self, expr: &Expression) {
                if expr == self.sub_target {
                    self.found = true;
                } else {
                    default_walk_expression(self, expr)
                }
            }
        }

        let mut finder = ExprFinder {
            sub_target,
            found: false,
        };
        finder.walk_expression(self);
        finder.found
    }
}

impl From<bool> for Constant {
    fn from(value: bool) -> Self {
        Self {
            value: value.into(),
            position: Position::default(),
        }
    }
}

impl From<bool> for Expression {
    fn from(value: bool) -> Self {
        Self::Constant(value.into())
    }
}
