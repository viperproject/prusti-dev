// Random extra example that I was working on
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
// TODO: Would be nice to get invariants working!
pub enum Tree {
    Leaf(i32, Box<Tree>, Box<Tree>, usize),
    Empty,
}
impl Default for Tree {
    fn default() -> Self { Tree::Empty }
}

impl Tree {
    predicate! {
    pub fn invariant_values(&self) -> bool {
        if let Tree::Leaf(value, left, right, _) = self {
            // Note that this relies on triggering; if I wanted to show that `left.value < self.value`
            // I would first have to trivially `assert!(left.find(left.value))`
            forall(|i: i32| left.find(i) == (i < *value && self.find(i))) &&
            forall(|i: i32| right.find(i) == (*value < i && self.find(i))) &&
            left.invariant_values() && right.invariant_values()
        } else { true }
    }
    }
    #[pure]
    pub fn find(&self, find_value: i32) -> bool {
        if let Tree::Leaf(value, left, right, _) = self {
            if find_value == *value { true }
            else if find_value < *value {
                left.find(find_value)
            } else {
                right.find(find_value)
            }
        } else { false }
    }

    // Height spec:
    #[requires(self.height() < usize::MAX)]
    #[requires(self.invariant_height())]
    #[ensures(self.invariant_height())]
    #[ensures(self.height() == old(self.height()) || self.height() == old(self.height()) + 1)]
    // Values spec:
    #[requires(self.invariant_values())]
    #[ensures(self.invariant_values())]
    #[ensures(self.find(new_value))]
    #[ensures(forall(|i: i32| i != new_value ==> old(self.find(i)) == self.find(i)))]
    pub fn insert(&mut self, new_value: i32) {
        match self {
            Tree::Leaf(value, left, right, _) => {
                if new_value < *value {
                    left.insert(new_value);
                    if left.height() > right.height() {
                        self.rebalance(new_value);
                    }
                } else if new_value > *value {
                    right.insert(new_value);
                    if right.height() > left.height() {
                        self.rebalance(new_value);
                    }
                } // (else new_value == *value) - we are done
            }
            Tree::Empty => {
                *self = Tree::Leaf(new_value, Box::new(Tree::Empty), Box::new(Tree::Empty), 1);
            }
        }
    }



    #[pure]
    pub fn height(&self) -> usize {
        if let Tree::Leaf(_, _, _, height) = self { *height }
        else { 0 }
    }
    #[pure]
    #[requires( matches!(self, Tree::Leaf(..)) )]
    pub fn value(&self) -> i32 {
        if let Tree::Leaf(value, _, _, _) = self { *value }
        else { unreachable!() }
    }
    #[pure]
    pub fn height_pair(left: &Tree, right: &Tree) -> (usize, usize) {
        let (lh, rh) = (left.height()+0, right.height()+0);
        if lh > rh { (lh, rh) } else { (rh, lh) }
    }

    #[pure]
    fn invariant_height(&self) -> bool {
        if let Tree::Leaf(_, left, right, height) = self {
            let (lh, rh) = (left.height(), right.height());
            *height >= 1 && (if lh > rh {
                *height - 1 == lh && lh - rh <= 1
            } else {
                *height - 1 == rh && rh - lh <= 1
            }) &&
            left.invariant_height() && right.invariant_height()
        } else { true }
    }
    #[pure]
    fn invariant_height_a(&self) -> bool {
        if let Tree::Leaf(_, left, right, _) = self {
            let (lh, rh) = (left.height(), right.height());
            (if lh > rh { lh - rh } else { rh - lh }) <= 2 &&
            left.invariant_height() && right.invariant_height()
        } else { true }
    }

    #[requires(self.invariant_values())]
    #[ensures(self.invariant_values())]
    #[ensures(forall(|i: i32| old(self.find(i)) == self.find(i)))]

    #[requires( matches!(self, Tree::Leaf(..)) )]
    #[requires(self.invariant_height_a())]
    #[ensures(self.invariant_height())]
    #[ensures(self.height() == old(self.height()) || self.height() == old(self.height()) + 1)]
    fn rebalance(&mut self, new_value: i32) {
        if let Tree::Leaf(_, left, right, height) = self {
            let (bh, sh) = Tree::height_pair(left, right);
            *height = bh + 1;
            if bh - sh > 1 {
                if left.height() > right.height() {
                    if left.value() < new_value {
                        left.left_rotate()
                    }
                    self.right_rotate()
                } else {
                    if new_value < right.value() {
                        right.right_rotate()
                    }
                    self.left_rotate()
                }
            }
        } else { unreachable!() }
    }

    #[trusted]
    #[requires(if let Tree::Leaf(_, _, right, _) = self {
        matches!(**right, Tree::Leaf(..)) && right.height() == self.height() - 1
    } else { false })]
    #[requires(self.invariant_values())]
    #[ensures(self.invariant_values())]
    #[ensures(forall(|i: i32| old(self.find(i)) == self.find(i)))]

    #[ensures(if let Tree::Leaf(_, left, _, _) = self {
        matches!(**left, Tree::Leaf(..)) && left.height() == self.height() - 1
    } else { false })]
    fn left_rotate(&mut self) {
        let root = std::mem::take(self);
        if let Tree::Leaf(sv, sl, right, _) = root {
            if let Tree::Leaf(rv, rl, rr, _) = *right {
                let lh = Tree::height_pair(&*sl, &*rl).0 + 1;
                let newl = Tree::Leaf(sv, sl, rl, lh);
                let newh = Tree::height_pair(&newl, &*rr).0 + 1;
                *self = Tree::Leaf(rv, Box::new(newl), rr, newh);
            } else { unreachable!() }
        } else { unreachable!() }
    }
    #[trusted]
    #[requires(self.invariant_values())]
    #[ensures(self.invariant_values())]
    #[ensures(forall(|i: i32| old(self.find(i)) == self.find(i)))]
    fn right_rotate(&mut self) {
        let root = std::mem::take(self);
        if let Tree::Leaf(sv, left, sr, _) = root {
            if let Tree::Leaf(lv, ll, lr, _) = *left {
                let rh = Tree::height_pair(&*lr, &*sr).0 + 1;
                let newr = Tree::Leaf(sv, lr, sr, rh);
                let newh = Tree::height_pair(&*ll, &newr).0 + 1;
                *self = Tree::Leaf(lv, ll, Box::new(newr), newh);
            } else { unreachable!() }
        } else { unreachable!() }
    }
}
