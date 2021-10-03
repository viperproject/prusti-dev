use super::typ::Type;

#[display(fmt = "{}: {}", name, typ)]
pub struct VariableDecl {
    pub name: String,
    pub typ: Type,
}
