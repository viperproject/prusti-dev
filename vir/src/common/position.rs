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
#[display(fmt = "({}, {})", line, column)]
pub struct Position {
    pub line: i32,
    pub column: i32,
    pub id: u64,
}

impl Position {
    pub fn new(line: i32, column: i32, id: u64) -> Self {
        Position { line, column, id }
    }
    pub fn line(&self) -> i32 {
        self.line
    }
    pub fn column(&self) -> i32 {
        self.column
    }
    pub fn id(&self) -> u64 {
        self.id
    }
    pub fn is_default(&self) -> bool {
        self.line == 0 && self.column == 0 && self.id == 0
    }
}

pub trait Positioned {
    fn position(&self) -> Position;
}
