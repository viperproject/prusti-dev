//! Adapted from https://github.com/nikomatsakis/nll-rfc/blob/master/0000-nonlexical-lifetimes.md

fn capitalize(vec: &mut [char]) {}

fn bar() {
    let mut data = vec!['a', 'b', 'c'];
    let slice = &mut data[..];
    capitalize(slice);
    data.push('d');
    data.push('e');
    data.push('f');
}
