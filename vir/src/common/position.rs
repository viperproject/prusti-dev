#[derive(
    Debug,
    derive_more::Display,
    Clone,
    Copy,
    Default,
    serde::Serialize,
    serde::Deserialize,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[display(fmt = "({})", id)]
pub struct Position {
    pub id: u64,
}

impl Position {
    pub fn new(id: u64) -> Self {
        Position { id }
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.id == 0
    }
}

pub trait Positioned {
    fn position(&self) -> Position;
}
