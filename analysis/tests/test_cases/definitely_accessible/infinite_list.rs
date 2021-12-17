struct InfiniteList {
    val: u32,
    next: Box<InfiniteList>
}

#[analyzer::run]
fn test1(mut a: InfiniteList) {
    let b = *a.next;
}

#[analyzer::run]
fn test2(mut x: InfiniteList) {
    x = *x.next.next;
}

fn main() {}
