struct Point { x: u32, y: u32 }

fn f1<'a>(p: &'a mut Point) -> &'a mut u32 {
    if p.x == 0 {
        &mut p.x
    } else {
        &mut p.x
    }
}

fn main() {}
