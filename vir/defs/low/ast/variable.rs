use super::ty::Type;

#[display(fmt = "{}: {}", name, ty)]
pub struct VariableDecl {
    pub name: String,
    pub ty: Type,
}
