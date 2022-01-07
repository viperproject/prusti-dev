#[derive(Copy, Default)]
#[display(fmt = "({}, {})", line, column)]
pub struct Position {
    pub line: i32,
    pub column: i32,
    pub id: u64,
}
