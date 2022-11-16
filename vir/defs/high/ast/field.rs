use super::ty::Type;

#[display(fmt = "{}({}): {}", name, index, ty)]
pub struct FieldDecl {
    pub name: String,
    pub index: usize,
    pub ty: Type,
}
