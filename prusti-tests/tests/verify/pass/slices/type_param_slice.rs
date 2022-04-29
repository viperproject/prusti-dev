fn foo<T: Ord> (bar: &mut [T]) {
    if bar.len() >= 1 {
        let _ = bar[0] == bar[0];
    }
}

fn main() {}
