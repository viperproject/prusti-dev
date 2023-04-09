use prusti_contracts::*;

#[cfg(feature = "prusti")]
fn main() {}
#[cfg(not(feature = "prusti"))]
fn main() {
    let mut t = Tree::Empty;
    for i in 0..=6 { t.insert(i); }
    println!("{:#?}", t);
}

#[cfg_attr(not(feature = "prusti"), derive(Debug))]
pub enum Tree {
    Node(i32, Box<Tree>, Box<Tree>),
    Empty,
}

impl Tree {
    predicate! {
    pub fn bst_invariant(&self) -> bool {
        if let Tree::Node(value, left, right) = self {
            // Note that this relies on triggering; if I wanted to show that `left.value < self.value`
            // I would first have to trivially `assert!(left.contains(left.value))`
            forall(|i: i32| left.contains(i) == (i < *value && self.contains(i))) &&
            forall(|i: i32| right.contains(i) == (*value < i && self.contains(i))) &&
            left.bst_invariant() && right.bst_invariant()
        } else { true }
    }
    }
    #[pure]
    pub fn contains(&self, find_value: i32) -> bool {
        if let Tree::Node(value, left, right) = self {
            if find_value == *value { true }
            else if find_value < *value {
                left.contains(find_value)
            } else {
                right.contains(find_value)
            }
        } else { false }
    }

    #[requires(self.bst_invariant())]
    #[ensures(self.bst_invariant())]
    #[ensures(self.contains(new_value))]
    #[ensures(forall(|i: i32| i != new_value ==> old(self.contains(i)) == self.contains(i)))]
    pub fn insert(&mut self, new_value: i32) {
        match self {
            Tree::Node(value, left, right) => {
                if new_value < *value {
                    left.insert(new_value);
                } else if new_value > *value {
                    right.insert(new_value);
                } // (else new_value == *value) - we are done
            }
            Tree::Empty => {
                *self = Tree::Node(new_value, Box::new(Tree::Empty), Box::new(Tree::Empty));
            }
        }
    }
}
