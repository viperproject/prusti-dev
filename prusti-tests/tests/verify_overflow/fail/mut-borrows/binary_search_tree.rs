use prusti_contracts::*;

mod tree {

    use prusti_contracts::*;

    pub struct Node {
        value: i32,
        left: Option<Box<Node>>,
        right: Option<Box<Node>>,
    }

    impl Node {
        #[pure]
        pub fn sorted(&self) -> bool {
            let left_sorted = if let Some(left) = &self.left {
                left.sorted() && left.value < self.value
            } else { true };
            let right_sorted = if let Some(right) = &self.right {
                right.sorted() && right.value >= self.value
            } else { true };
            left_sorted && right_sorted
        }

        #[pure]
        pub fn in_range(&self, value: i32) -> bool {
            let left_sorted = if let Some(left) = &self.left {
                left.value < value
            } else { true };
            let right_sorted = if let Some(right) = &self.right {
                right.value >= value
            } else { true };
            left_sorted && right_sorted
        }
        #[requires(self.sorted())]
        #[ensures(*result == old(self.value))]
        #[assert_on_expiry(
            old(self).in_range(*result),
            self.sorted()
        )]
        pub fn borrow_value(&mut self) -> &mut i32 {
            &mut self.value
        }
    }
}

use tree::Node;

#[requires(node.sorted())]
#[ensures(node.sorted())]
pub fn test1(node: &mut Node) {
    let value = node.borrow_value();     //~ ERROR: obligation might not hold on borrow expiry
    *value = 5;
}

#[requires(node.sorted())]
#[ensures(node.sorted())]
pub fn test2(node: &mut Node) {
    let value = node.borrow_value();
    let x = *value;
    *value = x;
}

fn main() {}
