derive_lower!(TypedToMiddleExpression, TypedToMiddleExpressionLowerer: typed::ast::expression::Expression => middle::ast::expression::Expression);
derive_lower!(TypedToMiddleStatement, TypedToMiddleStatementLowerer: typed::ast::statement::Statement => middle::ast::statement::Statement);
derive_lower!(TypedToMiddleRvalue, TypedToMiddleRvalueLowerer: typed::ast::rvalue::Rvalue => middle::ast::rvalue::Rvalue);
derive_lower!(TypedToMiddleTypeDecl, TypedToMiddleTypeDeclLowerer: typed::ast::type_decl::TypeDecl => middle::ast::type_decl::TypeDecl);
derive_lower!(TypedToMiddleType, TypedToMiddleTypeLowerer: typed::ast::ty::Type => middle::ast::ty::Type);
derive_lower!(MiddleToTypedType, MiddleToTypedTypeUpperer: middle::ast::ty::Type => typed::ast::ty::Type);
derive_lower!(TypedToMiddlePredicate, TypedToMiddlePredicateLowerer: typed::ast::predicate::Predicate => middle::ast::predicate::Predicate);
