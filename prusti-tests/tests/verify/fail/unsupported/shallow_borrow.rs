/// From the serde crate

fn iterator_len_hint<I>(iter: &I) -> Option<usize>
    where
        I: Iterator,
{
    match iter.size_hint() { //~ ERROR unsupported creation of shallow borrows (implicitly created when lowering matches)
        (lo, Some(hi)) if lo == hi => Some(lo),
        _ => None,
    }
}

fn main() {}
