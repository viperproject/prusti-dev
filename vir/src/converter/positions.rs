macro derive_from($from: ty, $to: ty) {
    impl From<$from> for $to {
        fn from(pos: $from) -> Self {
            Self {
                id: pos.id,
                line: pos.line,
                column: pos.column,
            }
        }
    }
}

derive_from!(crate::high::Position, crate::polymorphic::Position);
derive_from!(crate::polymorphic::Position, crate::high::Position);

derive_from!(crate::high::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::high::Position);

derive_from!(crate::polymorphic::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::polymorphic::Position);
