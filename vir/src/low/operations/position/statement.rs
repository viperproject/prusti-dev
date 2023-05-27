use super::super::super::ast::statement::*;
use crate::common::position::{Position, Positioned};

impl Positioned for Statement {
    fn position(&self) -> Position {
        match self {
            Self::Comment(statement) => statement.position(),
            Self::Label(statement) => statement.position(),
            Self::LogEvent(statement) => statement.position(),
            Self::Assume(statement) => statement.position(),
            Self::Assert(statement) => statement.position(),
            Self::Inhale(statement) => statement.position(),
            Self::Exhale(statement) => statement.position(),
            Self::Fold(statement) => statement.position(),
            Self::Unfold(statement) => statement.position(),
            Self::ApplyMagicWand(statement) => statement.position(),
            Self::MethodCall(statement) => statement.position(),
            Self::Assign(statement) => statement.position(),
            Self::Conditional(statement) => statement.position(),
            Self::MaterializePredicate(statement) => statement.position(),
        }
    }
}

impl Positioned for Comment {
    fn position(&self) -> Position {
        Default::default()
    }
}

impl Positioned for Label {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for LogEvent {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Assume {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Assert {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Inhale {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Exhale {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Fold {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Unfold {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for ApplyMagicWand {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for MethodCall {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Assign {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Conditional {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for MaterializePredicate {
    fn position(&self) -> Position {
        self.position
    }
}
