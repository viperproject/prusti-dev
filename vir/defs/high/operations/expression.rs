use super::{
    super::ast::{
        expression::{
            visitors::{
                default_fold_expression, default_fold_quantifier, default_walk_expression,
                ExpressionFolder, ExpressionWalker,
            },
            *,
        },
        position::Position,
    },
    ty::Typed,
};

impl From<VariableDecl> for Expression {
    fn from(variable: VariableDecl) -> Self {
        Self::local_no_pos(variable)
    }
}

impl Expression {
    /// Only defined for places.
    pub fn get_base(&self) -> VariableDecl {
        debug_assert!(self.is_place());
        match self {
            Expression::Local(Local { variable, .. }) => variable.clone(),
            Expression::LabelledOld(LabelledOld { base, .. }) => base.get_base(),
            _ => self.get_parent_ref().unwrap().get_base(),
        }
    }
    /// Only defined for places.
    pub fn get_parent_ref(&self) -> Option<&Expression> {
        debug_assert!(self.is_place());
        match self {
            Expression::Local(_) => None,
            Expression::Variant(Variant { box ref base, .. })
            | Expression::Field(Field { box ref base, .. })
            | Expression::AddrOf(AddrOf { box ref base, .. }) => Some(base),
            Expression::LabelledOld(_) => None,
            expr => unreachable!("{}", expr),
        }
    }
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
        if let Some(ty) = replacement.get_type().forget_variant() {
            assert_eq!(target.get_type(), &ty, "{} → {}", target, replacement);
        } else {
            assert_eq!(
                target.get_type(),
                replacement.get_type(),
                "{} → {}",
                target,
                replacement
            );
        }

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
    pub fn replace_multiple_places(self, replacements: &[(Expression, Expression)]) -> Self {
        struct PlaceReplacer<'a> {
            replacements: &'a [(Expression, Expression)],
        }
        impl<'a> ExpressionFolder for PlaceReplacer<'a> {
            fn fold_expression(&mut self, expression: Expression) -> Expression {
                if expression.is_place() {
                    // Check if this matches a substitution.
                    for (target, replacement) in self.replacements {
                        if target == &expression {
                            return replacement.clone();
                        }
                    }
                }
                // Otherwise, keep folding
                default_fold_expression(self, expression)
            }

            fn fold_quantifier(&mut self, quantifier: Quantifier) -> Expression {
                // TODO: the correct solution is the following:
                // (1) skip replacements where `src` uses a quantified variable;
                // (2) rename with a fresh name the quantified variables that conflict with `dst`.
                for (src, dst) in self.replacements.iter() {
                    if quantifier.variables.contains(&src.get_base())
                        || quantifier.variables.contains(&dst.get_base())
                    {
                        unimplemented!(
                            "replace_multiple_places doesn't handle replacements that conflict \
                            with quantified variables"
                        )
                    }
                }
                Expression::Quantifier(default_fold_quantifier(self, quantifier))
            }
        }
        PlaceReplacer { replacements }.fold_expression(self)
    }
    pub fn map_old_expression_label<F>(self, substitutor: F) -> Self
    where
        F: Fn(String) -> String,
    {
        struct OldExpressionLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            substitutor: T,
        }
        impl<T> ExpressionFolder for OldExpressionLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> Expression {
                Expression::LabelledOld(LabelledOld {
                    label: (self.substitutor)(label),
                    base,
                    position,
                })
            }
        }
        OldExpressionLabelSubstitutor { substitutor }.fold_expression(self)
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
    pub fn function_call<S: Into<String>>(
        name: S,
        arguments: Vec<Expression>,
        return_type: Type,
    ) -> Expression {
        let parameters = arguments
            .iter()
            .enumerate()
            .map(|(i, argument)| VariableDecl {
                name: format!("_{}", i),
                ty: argument.get_type().clone(),
            })
            .collect();
        Expression::func_app_no_pos(name.into(), arguments, parameters, return_type)
    }
    pub fn set_default_pos(self, new_position: Position) -> Self {
        struct DefaultPositionReplacer {
            new_position: Position,
        }
        impl ExpressionFolder for DefaultPositionReplacer {
            fn fold_position(&mut self, position: Position) -> Position {
                if position.is_default() {
                    self.new_position
                } else {
                    position
                }
            }
        }
        DefaultPositionReplacer { new_position }.fold_expression(self)
    }
}
