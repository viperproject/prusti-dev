use prusti_contracts::*;

struct Node {
    elem: i32,
    next: Option<Box<Node>>,
}

pub struct Stack {
    head: Option<Box<Node>>,
}

impl Stack {
    #[pure]
    #[trusted]
    fn len(&self) -> i32 {
        unimplemented!()
    }

    #[requires(0 < self.len())]
    fn top_node(&mut self) -> &mut Node {
        match self.head {
            None => { unreachable!() }, //~ ERROR unreachable!(..) statement might be reachable
            Some(ref mut node) => node,
        }
    }
}

#[trusted]
fn main() {}
