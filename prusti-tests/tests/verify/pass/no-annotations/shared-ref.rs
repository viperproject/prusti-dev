//! Source: https://docs.diesel.rs/src/matches/lib.rs.html#31-40


/// Work around "error: unexpected token: `an interpolated tt`", whatever that means.
macro_rules! _matches_tt_as_expr_hack {
    ($value:expr) => ($value)
}

/// Check if an expression matches a refutable pattern.
macro_rules! matches {
    ($expression:expr, $($pattern:tt)+) => {
        _matches_tt_as_expr_hack! {
            match $expression {
                $($pattern)+ => true,
                _ => false
            }
        }
    }
}

fn byte_serialized_unchanged(byte: u8) -> bool {
    matches!(byte, b'*' | b'-' | b'.' | b'0' ... b'9' | b'A' ... b'Z' | b'_' | b'a' ... b'z')
}

fn main(){}
