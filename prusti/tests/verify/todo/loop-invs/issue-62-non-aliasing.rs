//! Issue #62: "Non-aliasing info are needed"

extern crate prusti_contracts;

#[requires="n >= 0"]
#[ensures="result == old(n) * (1 + old(n) * old(k))"]
fn test(n: i32, k: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="res == ia * (1 + n * k)"]
    #[invariant="ia <= n"]
    while ia < n {
        res += 1;
        let mut ib = 0;

        #[invariant="res == ia * (1 + n * k) + 1 + ib * k"]
        #[invariant="ib <= n"]
        while ib < n {
            res += k;
            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {

}

/*

  label bb0
  // ========== bb0 ==========
  // [mir] StorageLive(_3)
  // [mir] _3 = const 0i32
  unfold acc(int(_3), 1 / 1)
  _3.val_int := 0
  // [mir] StorageLive(_4)
  // [mir] _4 = const 0i32
  unfold acc(int(_4), 1 / 1)
  _4.val_int := 0
  // [mir] goto -> bb2
  // Assert and exhale the loop invariant of block bb2
  unfold acc(int(_2), 1 / 1)
  assert _1.val_int >= 0
  assert _1 != _2
  assert _3.val_int == _4.val_int * (1 + _1.val_int * _2.val_int) && _4.val_int <= _1.val_int
  fold acc(int(_4), 1 / 1)
  fold acc(int(_1), 1 / 1)
  fold acc(int(_2), 1 / 1)
  fold acc(int(_3), 1 / 1)
  exhale acc(int(_7), 1 / 1) && acc(int(_8), 1 / 1) && acc(bool(_6), 1 / 1) && acc(ref$int(_13), 1 / 1) && acc(ref$int(_14), 1 / 1) && acc(ref$int(_15), 1 / 1) && acc(ref$int(_16), 1 / 1) && acc(ref$int(_18), 1 / 1) && acc(ref$int(_19), 1 / 1) && acc(tuple0$(_10), 1 / 1) && acc(tuple2$int$bool(_20), 1 / 1) && acc(int(_3), 1 / 1) && acc(int(_21), 1 / 1) && acc(int(_24), 1 / 1) && acc(int(_25), 1 / 1) && acc(bool(_23), 1 / 1) && acc(tuple0$(_22), 1 / 1) && acc(tuple2$int$bool(_40), 1 / 1) && acc(ref$int(_29), 1 / 1) && acc(ref$int(_30), 1 / 1) && acc(ref$int(_31), 1 / 1) && acc(ref$int(_32), 1 / 1) && acc(ref$int(_33), 1 / 1) && acc(ref$int(_35), 1 / 1) && acc(ref$int(_36), 1 / 1) && acc(tuple0$(_26), 1 / 1) && acc(int(_37), 1 / 1) && acc(tuple2$int$bool(_38), 1 / 1) && acc(tuple2$int$bool(_39), 1 / 1) && acc(tuple0$(_9), 1 / 1) && acc(int(_4), 1 / 1) && acc(int(_1), 3 / 4) && acc(int(_2), 3 / 4)
  assert _1 != _2                                        // <-- OK
  assert unfolding acc(int(_1), 1/4) in _1.val_int >= 0  // <-- DOES NOT WORK WITH 2/4, 3/4
  // begin frame
  goto bb2

*/
