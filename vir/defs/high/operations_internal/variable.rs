use super::super::ast::variable::*;

impl VariableDecl {
    #[must_use]
    pub fn erase_lifetime(self) -> Self {
        Self {
            name: self.name,
            ty: self.ty.erase_lifetimes(),
        }
    }
}
