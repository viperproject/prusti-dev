use prusti_contracts::*;

struct Child {
    v: u32,
}

struct Tree {
    child: Child,
}

#[pure]
fn use_child(_: &Child, _: &Tree, _: &Child) -> bool { true }

#[pure]
#[ensures(use_child(&result.child, result, &result.child))]
fn test(tree: &Tree) -> &Tree {
    tree
}

fn main() {}
