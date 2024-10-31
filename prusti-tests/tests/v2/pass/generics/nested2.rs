struct R(Option<Box<u32>>);
fn main() {
    match R(None).0 {
        Some(_) => (),
        _ => (),
    }
}
