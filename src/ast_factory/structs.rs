use jni::objects::JObject;

jobject_wrapper!(Type);
jobject_wrapper!(Expr);
jobject_wrapper!(Trigger);
jobject_wrapper!(Position);
jobject_wrapper!(Domain);
jobject_wrapper!(DomainFunc);
jobject_wrapper!(Function);
jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Field);
jobject_wrapper!(Predicate);
jobject_wrapper!(LocalVarDecl);
jobject_wrapper!(Stmt);

pub enum Location<'a> {
    Predicate(Predicate<'a>),
    Field(Field<'a>),
}
