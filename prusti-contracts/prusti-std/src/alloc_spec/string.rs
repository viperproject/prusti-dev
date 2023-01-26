use prusti_contracts::*;

use alloc::string::String;

// FUTURE(#1221): String should forward its specs to as_str where possible, to avoid writing each spec twice.
// That doesn't currently work though, due to issue #1221
#[extern_spec]
impl String {
    #[ensures(result.is_empty())]
    fn new() -> Self;

    #[pure]
    #[ensures(result == (self.len() == 0))]
    //#[ensures(result == self.as_str().is_empty()))]
    fn is_empty(&self) -> bool;

    #[pure]
    #[ensures(result.len() == self.len())]
    fn as_str(&self) -> &str;

    #[pure]
    //#[ensures(result == self.as_str().len())]
    fn len(&self) -> usize;

    #[ensures(self.len() == 0)]
    fn clear(&mut self);

    #[ensures(self.len() == old(self.len()) + 1)]
    //#[ensures(self[self.len() - 1] === ch)]
    //#[ensures(forall(|i: usize| i < old(self.len()) ==> self[i] === old(self[i])))]
    fn push(&mut self, ch: char);
}

#[extern_spec]
impl str {
    // TODO: this should be a prusti intrinsic, like it is for slices.
    #[pure]
    fn len(&self) -> usize;

    #[pure]
    #[ensures(result == (self.len() == 0))]
    fn is_empty(&self) -> bool;
}

// FUTURE(#1221): these specs make their methods crash due to issue #1221, so they are disabled for now.
/*
#[extern_spec]
impl Deref for String {
    #[ensures(result === self.as_str()]
    fn deref(&self) -> &str;
}

#[extern_spec]
impl ToOwned for str {
    #[ensures(result.as_str() === self)]
    fn to_owned(&self) -> String;
}

#[extern_spec]
impl ToString for str {
    #[ensures(result.as_str() === self)]
    fn to_string(&self) -> String;
}

#[extern_spec]
impl From<&str> for String {
    #[ensures(result.as_str() === other)]
    fn from(other: &str) -> Self;
}
*/

#[extern_spec]
impl Default for String {
    #[ensures(result.is_empty())]
    fn default() -> Self;
}
