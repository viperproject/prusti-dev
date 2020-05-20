#![feature(register_tool)]
#![register_tool(prusti)]

#[prusti::requires(x > 0)]
fn main() {
}
