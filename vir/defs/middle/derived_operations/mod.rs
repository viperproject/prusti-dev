derive_lower!(ToMiddleExpression, ToMiddleExpressionLowerer: high::ast::expression::Expression => middle::ast::expression::Expression);
derive_lower!(ToMiddleStatement, ToMiddleStatementLowerer: high::ast::statement::Statement => middle::ast::statement::Statement);
derive_lower!(ToMiddleRvalue, ToMiddleRvalueLowerer: high::ast::rvalue::Rvalue => middle::ast::rvalue::Rvalue);
derive_lower!(ToMiddleTypeDecl, ToMiddleTypeDeclLowerer: high::ast::type_decl::TypeDecl => middle::ast::type_decl::TypeDecl);
derive_lower!(ToMiddleType, ToMiddleTypeLowerer: high::ast::ty::Type => middle::ast::ty::Type);
derive_lower!(RestoreHighType, ToHighTypeUpperer: middle::ast::ty::Type => high::ast::ty::Type);
derive_lower!(ToMiddlePredicate, ToMiddlePredicateLowerer: high::ast::predicate::Predicate => middle::ast::predicate::Predicate);
