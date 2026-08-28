pub enum Void { }

pub fn unreachable(x: Box<Void>) -> ! {
    match *x {}
}

fn void_unwrap<T>(this: Result<T, Box<Void>>) -> T {
    match this {
        Ok(val) => val,
        Err(e) => unreachable(e)
    }
}

fn main() {}
