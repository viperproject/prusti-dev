use prusti_contracts::*;
use std::ptr;

pub struct VecWrapperI32 {
    _ghost_size: usize,
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        self._ghost_size as isize
    }

    #[trusted]
    #[requires(size > 0)]
    #[ensures (result.len() == size)]
    #[ensures (forall(|i: isize| (0 <= i && i < result.len()) ==> result.lookup(i) == 0))]
    pub fn new(size: isize) -> Self {
        Self {
            _ghost_size: size as usize,
            v: vec![0; size as usize],
        }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        self.v[index as usize]
    }

    #[trusted]
    #[requires(0 <= idx && idx < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(idx) == value)]
    #[ensures(forall(|i: isize|
        (0 <= i && i < self.len() && i != idx) ==>
        self.lookup(i) == old(self.lookup(i))))]
    pub fn set(&mut self, idx: isize, value: isize) -> () {
        self.v[idx as usize] = value
    }
}

#[pure]
#[requires(n >= 1)]
#[ensures(result >= 0)]
fn log(n: isize) -> isize {
    if n == 1 {
        0
    } else {
        1 + log(n / 2)
    }
}

#[pure]
#[requires(n >= 0)]
#[ensures(result > 0)]
fn pow(n: isize) -> isize {
    if n == 0 {
        1
    } else  {
        2 * pow(n - 1)
    }
}

#[pure]
#[trusted]
#[ensures((y % 2) == 0 ==> (x / (y / 2)) == (2 * x) / y)]
fn lemma(x: isize, y: isize) {

}

#[pure]
#[requires(power_of_two(len))]
#[requires(idx >= 1 && idx < len * 2)]
#[ensures(result >= 1)]
#[ensures(power_of_two(result))]
#[ensures(result == len / pow(log(idx)))]
#[ensures(idx < len  ==> result > 1)]
#[ensures(idx >= len ==> result == 1)]
fn range_length(idx: isize, len: isize) -> isize {
    if idx == 1 {
        assert!(len == len / pow(log(idx)));
        len
    } else {
        let x = range_length(idx / 2, len);
        let y = log(idx / 2);
        let z = log(idx);
        assert!(z == y + 1);
        let a = pow(y);
        let b = pow(z);
        assert!(b == a * 2);
        assert!(a == b / 2);
        assert!(x == len / a);
        let result = x / 2;
        assert!(x == len / (b / 2));
        assert!(b % 2 == 0);
        assert!(x == (2 * len) / b);
        assert!(x == (2 * len) / b);
        x / 2
    }
}

#[pure]
#[requires(power_of_two(array.len()))]
#[requires(power_of_two(rIdx - lIdx))]
#[requires(segTree.len() == array.len() * 2)]
#[requires(idx >= 1 && idx < segTree.len())]
#[requires(lIdx >= 0 && lIdx < rIdx && rIdx <= array.len())]
#[requires(rIdx - lIdx == range_length(idx, array.len()))]
#[ensures(result ==> segTree.lookup(idx) == array_range_sum(array,lIdx, rIdx))]
fn sum_property(
    array: &VecWrapperI32,
    segTree: &VecWrapperI32,
    idx: isize,
    lIdx: isize,
    rIdx: isize,
) -> bool {
    if idx >= array.len() {
        segTree.lookup(idx) == array.lookup(lIdx)
    } else {
        assert!((rIdx + lIdx) % 2 == 0);
        let mid = (rIdx + lIdx) / 2;
        assert!(mid * 2 == rIdx + lIdx);
        assert!((rIdx - mid) * 2 == (rIdx - lIdx));
        assert!((idx * 2 + 1) / 2 == idx);
        sum_property(array, segTree, idx * 2, lIdx, mid)
            && sum_property(array, segTree, idx * 2 + 1, mid, rIdx)
            && segTree.lookup(idx) == segTree.lookup(idx * 2) + segTree.lookup(idx * 2 + 1)
    }
}

#[pure]
#[ensures(result <= a && result <= b)]
#[ensures(result == a || result == b)]
fn min(a: isize, b: isize) -> isize {
    if a < b {
        a
    } else {
        b
    }
}

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: isize, b: isize) -> isize {
    if a > b {
        a
    } else {
        b
    }
}

#[pure]
#[requires(power_of_two(array.len()))]
#[requires(power_of_two(nodeRIdx - nodeLIdx))]
#[requires(segTree.len() == array.len() * 2)]
#[requires(idx >= 1 && idx < segTree.len())]
#[requires(nodeLIdx >= 0 && nodeLIdx < nodeRIdx && nodeRIdx <= array.len())]
#[requires(nodeRIdx - nodeLIdx == range_length(idx, array.len()))]
#[requires(sum_property(array, segTree, idx, nodeLIdx, nodeRIdx))]
#[requires(lIdx >= nodeLIdx && lIdx < rIdx && rIdx <= nodeRIdx)]
#[ensures(result == array_range_sum(array, lIdx, rIdx))]
fn range_sum(
    segTree: &VecWrapperI32,
    idx: isize,
    lIdx: isize,
    rIdx: isize,
    array: &VecWrapperI32,
    nodeLIdx: isize,
    nodeRIdx: isize,
) -> isize {
    if lIdx == nodeLIdx && rIdx == nodeRIdx {
        segTree.lookup(idx)
    } else {
        let mut result = 0;

        assert!((nodeRIdx + nodeLIdx) % 2 == 0);
        let mid = (nodeRIdx + nodeLIdx) / 2;
        assert!(mid * 2 == nodeRIdx + nodeLIdx);
        assert!((nodeRIdx - mid) * 2 == (nodeRIdx - nodeLIdx));

        if lIdx < mid {
            result += range_sum(
                segTree,
                idx * 2,
                lIdx,
                min(mid, rIdx),
                array,
                nodeLIdx,
                mid,
            );
        } else {
            result += 0;
        }

        if rIdx > mid {
            result += range_sum(
                segTree,
                idx * 2 + 1,
                max(mid, lIdx),
                rIdx,
                array,
                mid,
                nodeRIdx,
            );
        } else {
            result += 0;
        }

        result
    }
}

#[requires(array.len() > 0)]
#[requires(power_of_two(array.len()))]
#[ensures(power_of_two(result.len()))]
fn build(array: &VecWrapperI32) -> VecWrapperI32 {
    let mut result = VecWrapperI32::new(2 * array.len());
    let idx = result.len() - 1;
    while idx >= 1 {
        body_invariant!(idx < result.len() && idx >= 1);
        if idx >= array.len() {
            result.set(idx, array.lookup(idx - array.len()));
        } else {
            let v = result.lookup(idx * 2) + result.lookup(idx * 2 + 1);
            result.set(idx, v);
        }
    }
    result
}

#[pure]
fn power_of_two(v: isize) -> bool {
    if v == 1 {
        true
    } else {
        let even = (v % 2 == 0);
        even && power_of_two(v / 2)
    }
}

#[pure]
#[requires(lIdx >= 0 && rIdx <= array.len() && lIdx < rIdx)]
#[ensures(lIdx == rIdx - 1 ==> result == array.lookup(lIdx))]
#[ensures(forall(|i: isize| (i > lIdx && i < rIdx) ==> result == array_range_sum(array, lIdx, i) + array_range_sum(array, i, rIdx)))]
fn array_range_sum(array: &VecWrapperI32, lIdx: isize, rIdx: isize) -> isize {
    if lIdx == rIdx - 1 {
        array.lookup(lIdx)
    } else {
        array.lookup(lIdx) + array_range_sum(array, lIdx + 1, rIdx)
    }
}
