use crate::low::{ast::position::Position, cfg::method::MethodDecl};

impl MethodDecl {
    #[must_use]
    pub fn set_default_position(self, new_position: Position) -> Self {
        Self {
            pres: self
                .pres
                .into_iter()
                .map(|expression| expression.set_default_position(new_position))
                .collect(),
            posts: self
                .posts
                .into_iter()
                .map(|expression| expression.set_default_position(new_position))
                .collect(),
            body: self.body.map(|statements| {
                statements
                    .into_iter()
                    .map(|statement| statement.set_default_position(new_position))
                    .collect()
            }),
            ..self
        }
    }
}
