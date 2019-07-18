#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

struct List {
    value: u32,
    next: Option<Box<List>>,
}

impl List {

    #[pure]
    #[requires="0 <= index && index < self.len()"]
    fn lookup(&self, index: usize) -> u32 {
        if index == 0 {
            self.value
        } else {
            match self.next {
                Some(box ref tail) => tail.lookup(index - 1),
                None => unreachable!()
            }
        }
    }

    #[pure]
    #[ensures="result >= 1"]
    fn len(&self) -> usize {
        match self.next {
            None => 1,
            Some(box ref tail) => 1 + tail.len()
        }
    }

    /// Returns the last node of the linked list. Recursive implementation.
    #[ensures="result.len() == 1"]
    #[ensures="result.value == old(self.lookup(self.len() - 1))"]
    #[ensures="
        after_expiry<result>(
            self.len() == old(self.len()) - 1 + before_expiry(result.len()) &&
            (forall i: usize ::
                (0 <= i && i < old(self.len()) - 1) ==>
                self.lookup(i) == old(self.lookup(i))) &&
            (forall i: usize ::
                (0 <= i && i < before_expiry(result.len())) ==>
                self.lookup(old(self.len()) - 1 + i) == before_expiry(result.lookup(i)))
        )
    "]
    fn recursive_get_last_mut(&mut self) -> &mut List {
        match self.next {
            None => self,
            Some(box ref mut next) => next.recursive_get_last_mut()
        }
    }

    /// Returns the last node of the linked list. Recursive implementation.
    #[ensures="result.len() == 1"]
    #[ensures="result.value == old(self.lookup(self.len() - 1))"]
    fn recursive_get_last(&self) -> &List {
        match self.next {
            None => self,
            Some(box ref next) => next.recursive_get_last()
        }
    }

    /// Appends a value at the end of a linked list
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="value == self.lookup(self.len() - 1)"]
    #[ensures="forall i: usize ::
                (0 <= i && i < old(self.len())) ==>
                self.lookup(i) == old(self.lookup(i))"]
    fn append(&mut self, value: u32) {
        let len = self.len();
        let last = self.recursive_get_last_mut();
        match last.next {
            Some(_) => unreachable!(),
            None => {},
        }
        last.next = Some(box List {
            next: None,
            value: value,
        });
        let old_last_value = last.value;
        assert!(last.lookup(1) == value);
        assert!(last.lookup(0) == old_last_value);
        assert!(self.lookup(len-1) == old_last_value);
        assert!(self.lookup(len) == value);
    }

}

fn main() {}
