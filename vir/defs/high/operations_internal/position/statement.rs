use super::super::super::ast::statement::*;
use crate::common::position::Positioned;

impl Positioned for Statement {
    fn position(&self) -> Position {
        match self {
            Self::Comment(statement) => statement.position(),
            Self::OldLabel(statement) => statement.position(),
            Self::Inhale(statement) => statement.position(),
            Self::Exhale(statement) => statement.position(),
            Self::Assume(statement) => statement.position(),
            Self::Assert(statement) => statement.position(),
            Self::MovePlace(statement) => statement.position(),
            Self::CopyPlace(statement) => statement.position(),
            Self::WritePlace(statement) => statement.position(),
            Self::WriteAddress(statement) => statement.position(),
            Self::Assign(statement) => statement.position(),
            Self::Consume(statement) => statement.position(),
            Self::LeakAll(statement) => statement.position(),
            Self::SetUnionVariant(statement) => statement.position(),
            Self::NewLft(statement) => statement.position(),
            Self::EndLft(statement) => statement.position(),
            Self::GhostAssignment(statement) => statement.position(),
            Self::LifetimeTake(statement) => statement.position(),
            Self::OpenMutRef(statement) => statement.position(),
            Self::CloseMutRef(statement) => statement.position(),
        }
    }
}

impl Positioned for Comment {
    fn position(&self) -> Position {
        Default::default()
    }
}

impl Positioned for OldLabel {
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

impl Positioned for MovePlace {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for CopyPlace {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for WritePlace {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for WriteAddress {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Assign {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for Consume {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for LeakAll {
    fn position(&self) -> Position {
        Default::default()
    }
}

impl Positioned for SetUnionVariant {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for NewLft {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for EndLft {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for GhostAssignment {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for LifetimeTake {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for OpenMutRef {
    fn position(&self) -> Position {
        self.position
    }
}

impl Positioned for CloseMutRef {
    fn position(&self) -> Position {
        self.position
    }
}
