#[derive(Copy, Default)]
#[display(fmt = "({}, {})", line, column)]
pub struct Position {
    line: i32,
    column: i32,
    id: u64,
}
