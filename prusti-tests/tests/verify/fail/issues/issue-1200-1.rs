use prusti_contracts::*;
use std::cmp::min;

/// Find a fft length larger that is at least `minimum_size` in length that is made up of a limited set of factors.
/// The `once_factor` will be used exactly once, the multi factors may be used any number of times to reach the minimum.
fn fast_fft_len(
    minimum_len: usize,
    once_factor: usize,
    multi_factor1: usize,
    multi_factor2: usize,
) -> usize {
    // Apply once factor
    let mut product = once_factor;

    // apply second factor until at or above minimum
    while product < minimum_len {
        product *= multi_factor2
    }

    // remove second factor one at a time then add enough first factor to reach minimum_size
    // repeat while tracking lowest viable product
    let mut best = product;
    loop {
        match product.cmp(&minimum_len) {
            std::cmp::Ordering::Less => product *= multi_factor1,
            std::cmp::Ordering::Equal => return product,
            std::cmp::Ordering::Greater => {
                best = min(best, product);
                if product % multi_factor2 != 0 { //~ ERROR attempt to calculate the remainder with a divisor of zero
                    return best;
                }
                product /= multi_factor2;
            }
        }
    }
}

fn main(){}
