use prusti_contracts::*;

struct Child {}

struct Tree {
    child: Child,
}

#[pure]
fn use_both(_: &Tree, _: &Child) -> bool {true}

#[pure]
fn test(tree: &Tree) -> bool {
    use_both(tree, &tree.child)
}

fn main() {}
