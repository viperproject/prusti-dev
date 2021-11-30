use prusti_contracts::*;

pub struct PageIndex {
    entry_count: isize,
}

impl PageIndex {
    #[pure]
    #[ensures(self.entry_count == isize::MIN ==> result == 0)]
    #[ensures(self.entry_count == 0 ==> result == 0)]
    #[ensures(result <= isize::MAX as usize)]
    pub const fn len(&self) -> usize {
        if self.entry_count < 0 {
            ((1_isize + self.entry_count) + isize::MAX) as usize
        } else {
            self.entry_count as usize
            
        }
    }

    #[pure]
    #[ensures(result == (self.len() == 0))]
    pub const fn is_empty(&self) -> bool {
        self.entry_count == isize::MIN || self.entry_count == 0
    }

    #[pure]
    pub const fn foo(&self) -> bool {
        self.len() < 4
    }

    #[requires(self.foo())]
    pub const fn bar(&self) -> bool {
        !self.is_empty()
    }
}

fn main() {}
