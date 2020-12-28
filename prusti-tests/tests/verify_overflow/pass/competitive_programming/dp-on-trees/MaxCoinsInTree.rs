use prusti_contracts::*;

pub struct Tree<'a> {
    coins: isize,
    children: Vec<&'a Tree<'a>>,
}

impl<'a> Tree<'a> {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn child_count(&self) -> isize {
        self.children.len() as isize
    }

    #[trusted]
    #[pure]
    #[ensures (result == self.coins)]
    pub fn coins(&self) -> isize {
        self.coins
    }

    #[trusted]
    #[ensures (result.child_count() == 0)]
    #[ensures (result.coins() == c)]
    pub fn new(c: isize) -> Self {
        Tree { coins: c,
            children: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.child_count())]
    pub fn child(&self, index: isize) -> &'a Tree {
       self.children[index as usize]
    }
}

pub struct VecWrapperI32 {
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        self.v.len() as isize
    }

    #[trusted]
    #[ensures (result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32 { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        self.v[index as usize]
    }

    #[trusted]
    #[ensures (self.len() == old(self.len()) + 1)]
    #[ensures (self.lookup(old(self.len())) == value)]
    #[ensures (forall(|i: isize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: isize) {
        self.v.push(value);
    }
}

#[pure]
#[ensures (result >= a && result >= b)]
#[ensures (result == a || result == b)]
fn max(a: isize, b: isize) -> isize {
    if a > b {
        a
    } else {
        b
    }
}

#[pure]
#[ensures(result == a + 1)]
fn inc(a: isize) -> isize {
    a + 1
}

#[pure]
#[requires(node.child_count() >= 0)]
#[requires(index >= 0 && index <= node.child_count())]
fn solve1_rec<'a>(node: &'a Tree, index: isize) -> isize {
    let c = node.child_count();
    if index == c {
        node.coins()
    } else {
        let child = node.child(index);
        solve1_rec(node, inc(index)) + solve2_rec(child, 0isize)
    }
}

#[pure]
#[requires(node.child_count() >= 0)]
#[requires(index >= 0 && index <= node.child_count())]
fn solve2_rec<'a>(node: &'a Tree, index: isize) -> isize {
    let c = node.child_count();
    if index == c {
        0isize
    } else {
        let child = node.child(index);
        solve2_rec(node, inc(index)) + max(solve1_rec(child, 0isize), solve2_rec(child, 0isize))
    }
}

fn main() {

}