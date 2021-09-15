use prusti_contracts::*;

struct List {
    head: Link,
}

enum Link {
    Empty,
    More,
}

#[trusted]
#[pure]
fn len(x: &Link) -> usize {
    unimplemented!()
}

#[trusted]
#[ensures(len(dest) > 123)]
fn replace(dest: &mut Link, src: ()) -> Link {
    unimplemented!()
}

fn pop(s: &mut Link) {
    replace(s, ());
}

#[trusted]
fn main() {}
