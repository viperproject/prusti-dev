use jni::objects::JObject;

jobject_wrapper!(Type);
jobject_wrapper!(Expr);
jobject_wrapper!(Trigger);
jobject_wrapper!(Position);
jobject_wrapper!(Domain);
jobject_wrapper!(DomainFunc);
jobject_wrapper!(DomainAxiom);
jobject_wrapper!(Function);
jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Field);
jobject_wrapper!(Predicate);
jobject_wrapper!(LocalVarDecl);
jobject_wrapper!(Stmt);

jobject_wrapper!(Location);
generate_conversion_from_to!(Predicate, Location);
generate_conversion_from_to!(Field, Location);

jobject_wrapper!(Declaration);
generate_conversion_from_to!(Stmt, Declaration);
generate_conversion_from_to!(LocalVarDecl, Declaration);
