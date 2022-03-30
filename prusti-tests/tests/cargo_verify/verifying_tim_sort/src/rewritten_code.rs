use std::vec::Vec;

pub fn main() {
    let mut x : [i32; 50] = [5; 50];
    merge_sort(&mut x);
}

fn insert_head(v: &mut [i32]) {
    if v.len() >= 2 && (v[1] < v[0]) {
        let tmp = v[0];
        v[0] = v[1];
        let mut i = 2;
        while i < v.len() {
            if !(i < v.len() && v[i] < tmp) {
                break;
            }
            v[i - 1] = v[i];
            i += 1;
        }
        v[i - 1] = tmp;
    }
}

fn merge(v: &mut [i32], mid: usize, buf: &mut Vec<i32>) {
    let len = v.len();

    if mid <= len - mid {
        let mut i = 0;
        while i < mid {
            buf.push(v[i]);
            i += 1;
        }

        let mut left = 0;
        let mut right = mid;
        let mut out = 0;
        
        while left < mid && right < len {
            if v[right] < v[left] {
                v[out] = v[right];
                right += 1;
            } else {
                v[out] = buf[left];
                left += 1;
            }
            out += 1;
        }

        while left < mid {
            v[out] = buf[left];
            out += 1;
            left += 1;
        }

    } else {
        let mut i = mid;
        while i < len {
            buf.push(v[i]);
            i += 1;
        }

        let mut left = mid;
        let mut right = len - mid;
        let mut out = len;

        while v[0] < v[left] && buf[0] < buf[right] {
            out -= 1;
            if buf[right - 1] < v[left - 1] {
                left -= 1;
                v[out] = v[left];
            } else {
                right -= 1;
                v[out] = buf[right];
            }
        }

        let mut i = 0;
        while i < right {
            v[left] = buf[i];
            i += 1;
            left += 1;
        }
    }
}

#[derive(Clone, Copy)]
struct Run {
    start: usize,
    len: usize,
}

fn collapse(runs: &[Run]) -> usize {
    let n = runs.len();
    if n >= 2
        && (runs[n - 1].start == 0
            || runs[n - 2].len <= runs[n - 1].len
            || (n >= 3 && runs[n - 3].len <= runs[n - 2].len + runs[n - 1].len)
            || (n >= 4 && runs[n - 4].len <= runs[n - 3].len + runs[n - 2].len))
    {
        if n >= 3 && runs[n - 3].len < runs[n - 1].len { n - 3 } else { n - 2 }
    } else {
        n
    }
}

fn merge_sort(v: &mut [i32]) {
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;

    if v.len() == 0 {
        return;
    }

    let len = v.len();

    if len <= MAX_INSERTION {
        if len >= 2 {
            let mut i = len - 2;
            loop {
                insert_head(&mut v[i..]);
                if i == 0 {
                    break;
                } else {
                    i -= 1;
                }
            }
        }
        return;
    }

    let mut buf = Vec::with_capacity(len / 2);

    let mut runs = vec![];
    let mut end = len;
    while end > 0 {
        let mut start = end - 1;
        if start > 0 {
            start -= 1;
                if v.get(start + 1) < v.get(start) {
                    while start > 0 && v.get(start) < v.get(start - 1) {
                        start -= 1;
                    }
                    v[start..end].reverse();
                } else {
                    while start > 0 && !(v.get(start) < v.get(start - 1))
                    {
                        start -= 1;
                    }
                }
        }

        while start > 0 && end - start < MIN_RUN {
            start -= 1;
            insert_head(&mut v[start..end]);
        }

        runs.push(Run { start, len: end - start });
        end = start;

        loop {
            let r = collapse(&runs);
            if r == runs.len() {
                break;
            }
            let left = runs[r + 1];
            let right = runs[r];
            merge(
                &mut v[left.start..right.start + right.len],
                left.len,
                &mut buf,
            );
            runs[r] = Run { start: left.start, len: left.len + right.len };
            runs.remove(r + 1);
        }
    }

    debug_assert!(runs.len() == 1 && runs[0].start == 0 && runs[0].len == len);
}