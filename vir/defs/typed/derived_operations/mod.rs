derive_lower!(mut HighToTypedExpression, HighToTypedExpressionLowerer: high::ast::expression::Expression => typed::ast::expression::Expression);
derive_lower!(mut HighToTypedStatement, HighToTypedStatementLowerer: high::ast::statement::Statement => typed::ast::statement::Statement);
derive_lower!(mut HighToTypedRvalue, HighToTypedRvalueLowerer: high::ast::rvalue::Rvalue => typed::ast::rvalue::Rvalue);
derive_lower!(mut HighToTypedTypeDecl, HighToTypedTypeDeclLowerer: high::ast::type_decl::TypeDecl => typed::ast::type_decl::TypeDecl);
derive_lower!(mut HighToTypedType, HighToTypedTypeLowerer: high::ast::ty::Type => typed::ast::ty::Type);
derive_lower!(mut TypedToHighType, TypedToHighTypeUpperer: typed::ast::ty::Type => high::ast::ty::Type);
derive_lower!(mut HighToTypedPredicate, HighToTypedPredicateLowerer: high::ast::predicate::Predicate => typed::ast::predicate::Predicate);
