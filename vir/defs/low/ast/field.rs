use super::ty::Type;

#[display(fmt = "{}: {}", name, ty)]
pub struct FieldDecl {
    pub name: String,
    pub ty: Type,
}
