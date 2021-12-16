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

derive_from!(crate::high::Position, crate::middle::Position);
derive_from!(crate::middle::Position, crate::high::Position);

derive_from!(crate::high::Position, crate::polymorphic::Position);
derive_from!(crate::polymorphic::Position, crate::high::Position);

derive_from!(crate::high::Position, crate::snapshot::Position);
derive_from!(crate::snapshot::Position, crate::high::Position);

derive_from!(crate::high::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::high::Position);

derive_from!(crate::high::Position, crate::low::Position);
derive_from!(crate::low::Position, crate::high::Position);

derive_from!(crate::middle::Position, crate::polymorphic::Position);
derive_from!(crate::polymorphic::Position, crate::middle::Position);

derive_from!(crate::middle::Position, crate::snapshot::Position);
derive_from!(crate::snapshot::Position, crate::middle::Position);

derive_from!(crate::middle::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::middle::Position);

derive_from!(crate::middle::Position, crate::low::Position);
derive_from!(crate::low::Position, crate::middle::Position);

derive_from!(crate::polymorphic::Position, crate::snapshot::Position);
derive_from!(crate::snapshot::Position, crate::polymorphic::Position);

derive_from!(crate::polymorphic::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::polymorphic::Position);

derive_from!(crate::polymorphic::Position, crate::low::Position);
derive_from!(crate::low::Position, crate::polymorphic::Position);

derive_from!(crate::snapshot::Position, crate::legacy::Position);
derive_from!(crate::legacy::Position, crate::snapshot::Position);

derive_from!(crate::snapshot::Position, crate::low::Position);
derive_from!(crate::low::Position, crate::snapshot::Position);

derive_from!(crate::legacy::Position, crate::low::Position);
derive_from!(crate::low::Position, crate::legacy::Position);
