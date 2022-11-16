pub enum Void { }

pub fn unreachable(x: Void) -> ! {
    match x {}
}

fn void_unwrap<T>(this: Result<T, Void>) -> T {
    match this {
        Ok(val) => val,
        Err(e) => unreachable(e)
    }
}

fn main() {}
