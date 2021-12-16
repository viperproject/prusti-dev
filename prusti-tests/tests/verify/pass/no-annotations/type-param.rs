/// From crate `050_chrono`
/// https://github.com/chronotope/chrono/blob/master/src/format/parsed.rs

/// Checks if `old` is either empty or has the same value to `new` (i.e. "consistent"),
/// and if it is empty, set `old` to `new` as well.
fn set_if_consistent<T: PartialEq>(old: &mut Option<T>, new: T) -> Option<()> {
    if let Some(ref old) = *old {
        if *old == new { Some(()) } else { None }
    } else {
        *old = Some(new);
        Some(())
    }
}

fn main() {}
