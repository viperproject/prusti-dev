use std::hash::Hash;
use std::collections::HashSet;

#[derive(Debug, Copy, Clone)]
pub struct UnorderedSetEq<'a, T: 'a>(pub &'a [T]);

impl<'a, T> PartialEq for UnorderedSetEq<'a, T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        let a: HashSet<_> = self.0.iter().collect();
        let b: HashSet<_> = other.0.iter().collect();

        a == b
    }
}
