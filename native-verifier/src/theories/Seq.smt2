
; ===== Sequence theory for type TYPENAME =====

(declare-sort Seq<TYPENAME> 0)

(declare-fun Seq_length (Seq<TYPENAME>) Int)
(declare-const Seq_empty Seq<TYPENAME>)
(declare-fun Seq_singleton (TYPENAME) Seq<TYPENAME>)
(declare-fun Seq_build (Seq<TYPENAME> TYPENAME) Seq<TYPENAME>)
(declare-fun Seq_index (Seq<TYPENAME> Int) TYPENAME)
(declare-fun Seq_append (Seq<TYPENAME> Seq<TYPENAME>) Seq<TYPENAME>)
(declare-fun Seq_update (Seq<TYPENAME> Int TYPENAME) Seq<TYPENAME>)
(declare-fun Seq_contains (Seq<TYPENAME> TYPENAME) Bool)
(declare-fun Seq_take (Seq<TYPENAME> Int) Seq<TYPENAME>)
(declare-fun Seq_drop (Seq<TYPENAME> Int) Seq<TYPENAME>)
(declare-fun Seq_equal (Seq<TYPENAME> Seq<TYPENAME>) Bool)
(declare-fun Seq_sameuntil (Seq<TYPENAME> Seq<TYPENAME> Int) Bool)

(assert (forall ((s Seq<TYPENAME>)) (!
  (<= 0 (Seq_length s))
  :pattern ((Seq_length s))
  :qid |$Seq[TYPENAME]_prog.seq_length_non_negative|)))
(assert (= (Seq_length (as Seq_empty  Seq<TYPENAME>)) 0))
(assert (forall ((s Seq<TYPENAME>)) (!
  (=> (= (Seq_length s) 0) (= s (as Seq_empty  Seq<TYPENAME>)))
  :pattern ((Seq_length s))
  :qid |$Seq[TYPENAME]_prog.only_empty_seq_length_zero|)))
(assert (forall ((e TYPENAME)) (!
  (= (Seq_length (Seq_singleton e)) 1)
  :pattern ((Seq_length (Seq_singleton e)))
  :qid |$Seq[TYPENAME]_prog.length_singleton_seq|)))
(assert (forall ((s Seq<TYPENAME>) (e TYPENAME)) (!
  (= (Seq_length (Seq_build s e)) (+ 1 (Seq_length s)))
  :pattern ((Seq_length (Seq_build s e)))
  :qid |$Seq[TYPENAME]_prog.length_seq_build_inc_by_one|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME)) (!
  (ite
    (= i (Seq_length s))
    (= (Seq_index (Seq_build s e) i) e)
    (= (Seq_index (Seq_build s e) i) (Seq_index s i)))
  :pattern ((Seq_index (Seq_build s e) i))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_build|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>)) (!
  (=>
    (and
      (not (= s1 (as Seq_empty  Seq<TYPENAME>)))
      (not (= s2 (as Seq_empty  Seq<TYPENAME>))))
    (= (Seq_length (Seq_append s1 s2)) (+ (Seq_length s1) (Seq_length s2))))
  :pattern ((Seq_length (Seq_append s1 s2)))
  :qid |$Seq[TYPENAME]_prog.seq_length_over_append|)))
(assert (forall ((e TYPENAME)) (!
  (= (Seq_index (Seq_singleton e) 0) e)
  :pattern ((Seq_singleton e))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_singleton|)))
(assert (forall ((e1 TYPENAME) (e2 TYPENAME)) (!
  (= (Seq_contains (Seq_singleton e1) e2) (= e1 e2))
  :pattern ((Seq_contains (Seq_singleton e1) e2))
  :qid |$Seq[TYPENAME]_prog.seq_contains_over_singleton|)))
(assert (forall ((s Seq<TYPENAME>)) (!
  (= (Seq_append (as Seq_empty  Seq<TYPENAME>) s) s)
  :pattern ((Seq_append (as Seq_empty  Seq<TYPENAME>) s))
  :qid |$Seq[TYPENAME]_prog.seq_append_empty_left|)))
(assert (forall ((s Seq<TYPENAME>)) (!
  (= (Seq_append s (as Seq_empty  Seq<TYPENAME>)) s)
  :pattern ((Seq_append s (as Seq_empty  Seq<TYPENAME>)))
  :qid |$Seq[TYPENAME]_prog.seq_append_empty_right|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>) (i Int)) (!
  (=>
    (and
      (not (= s1 (as Seq_empty  Seq<TYPENAME>)))
      (not (= s2 (as Seq_empty  Seq<TYPENAME>))))
    (ite
      (< i (Seq_length s1))
      (= (Seq_index (Seq_append s1 s2) i) (Seq_index s1 i))
      (= (Seq_index (Seq_append s1 s2) i) (Seq_index s2 (- i (Seq_length s1))))))
  :pattern ((Seq_index (Seq_append s1 s2) i))
  :pattern ((Seq_index s1 i) (Seq_append s1 s2))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_append|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME)) (!
  (=>
    (and (<= 0 i) (< i (Seq_length s)))
    (= (Seq_length (Seq_update s i e)) (Seq_length s)))
  :pattern ((Seq_length (Seq_update s i e)))
  :qid |$Seq[TYPENAME]_prog.seq_length_invariant_over_update|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME) (j Int)) (!
  (ite
    (=> (and (<= 0 i) (< i (Seq_length s))) (= i j))
    (= (Seq_index (Seq_update s i e) j) e)
    (= (Seq_index (Seq_update s i e) j) (Seq_index s j)))
  :pattern ((Seq_index (Seq_update s i e) j))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_update|)))
(assert (forall ((s Seq<TYPENAME>) (e TYPENAME)) (!
  (=
    (Seq_contains s e)
    (exists ((i Int)) (!
      (and (<= 0 i) (and (< i (Seq_length s)) (= (Seq_index s i) e)))
      :pattern ((Seq_index s i))
      )))
  :pattern ((Seq_contains s e))
  :qid |$Seq[TYPENAME]_prog.seq_element_contains_index_exists|)))
(assert (forall ((e TYPENAME)) (!
  (not (Seq_contains (as Seq_empty  Seq<TYPENAME>) e))
  :pattern ((Seq_contains (as Seq_empty  Seq<TYPENAME>) e))
  :qid |$Seq[TYPENAME]_prog.empty_seq_contains_nothing|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>) (e TYPENAME)) (!
  (=
    (Seq_contains (Seq_append s1 s2) e)
    (or (Seq_contains s1 e) (Seq_contains s2 e)))
  :pattern ((Seq_contains (Seq_append s1 s2) e))
  :qid |$Seq[TYPENAME]_prog.seq_contains_over_append|)))
(assert (forall ((s Seq<TYPENAME>) (e1 TYPENAME) (e2 TYPENAME)) (!
  (= (Seq_contains (Seq_build s e1) e2) (or (= e1 e2) (Seq_contains s e2)))
  :pattern ((Seq_contains (Seq_build s e1) e2))
  :qid |$Seq[TYPENAME]_prog.seq_contains_over_build|)))
(assert (forall ((s Seq<TYPENAME>) (n Int)) (!
  (=> (<= n 0) (= (Seq_take s n) (as Seq_empty  Seq<TYPENAME>)))
  :pattern ((Seq_take s n))
  :qid |$Seq[TYPENAME]_prog.seq_take_negative_length|)))
(assert (forall ((s Seq<TYPENAME>) (n Int) (e TYPENAME)) (!
  (=
    (Seq_contains (Seq_take s n) e)
    (exists ((i Int)) (!
      (and
        (<= 0 i)
        (and (< i n) (and (< i (Seq_length s)) (= (Seq_index s i) e))))
      :pattern ((Seq_index s i))
      )))
  :pattern ((Seq_contains (Seq_take s n) e))
  :qid |$Seq[TYPENAME]_prog.seq_contains_over_take_index_exists|)))
(assert (forall ((s Seq<TYPENAME>) (n Int)) (!
  (=> (<= n 0) (= (Seq_drop s n) s))
  :pattern ((Seq_drop s n))
  :qid |$Seq[TYPENAME]_prog.seq_drop_negative_length|)))
(assert (forall ((s Seq<TYPENAME>) (n Int) (e TYPENAME)) (!
  (=
    (Seq_contains (Seq_drop s n) e)
    (exists ((i Int)) (!
      (and
        (<= 0 i)
        (and (<= n i) (and (< i (Seq_length s)) (= (Seq_index s i) e))))
      :pattern ((Seq_index s i))
      )))
  :pattern ((Seq_contains (Seq_drop s n) e))
  :qid |$Seq[TYPENAME]_prog.seq_contains_over_drop_index_exists|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>)) (!
  (=
    (Seq_equal s1 s2)
    (and
      (= (Seq_length s1) (Seq_length s2))
      (forall ((i Int)) (!
        (=>
          (and (<= 0 i) (< i (Seq_length s1)))
          (= (Seq_index s1 i) (Seq_index s2 i)))
        :pattern ((Seq_index s1 i))
        :pattern ((Seq_index s2 i))
        ))))
  :pattern ((Seq_equal s1 s2))
  :qid |$Seq[TYPENAME]_prog.extensional_seq_equality|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>)) (!
  (=> (Seq_equal s1 s2) (= s1 s2))
  :pattern ((Seq_equal s1 s2))
  :qid |$Seq[TYPENAME]_prog.seq_equality_identity|)))
(assert (forall ((s1 Seq<TYPENAME>) (s2 Seq<TYPENAME>) (n Int)) (!
  (=
    (Seq_sameuntil s1 s2 n)
    (forall ((i Int)) (!
      (=> (and (<= 0 i) (< i n)) (= (Seq_index s1 i) (Seq_index s2 i)))
      :pattern ((Seq_index s1 i))
      :pattern ((Seq_index s2 i))
      )))
  :pattern ((Seq_sameuntil s1 s2 n))
  :qid |$Seq[TYPENAME]_prog.extensional_seq_equality_prefix|)))
(assert (forall ((s Seq<TYPENAME>) (n Int)) (!
  (=>
    (<= 0 n)
    (ite
      (<= n (Seq_length s))
      (= (Seq_length (Seq_take s n)) n)
      (= (Seq_length (Seq_take s n)) (Seq_length s))))
  :pattern ((Seq_length (Seq_take s n)))
  :qid |$Seq[TYPENAME]_prog.seq_length_over_take|)))
(assert (forall ((s Seq<TYPENAME>) (n Int) (i Int)) (!
  (=>
    (and (<= 0 i) (and (< i n) (< i (Seq_length s))))
    (= (Seq_index (Seq_take s n) i) (Seq_index s i)))
  :pattern ((Seq_index (Seq_take s n) i))
  :pattern ((Seq_index s i) (Seq_take s n))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_take|)))
(assert (forall ((s Seq<TYPENAME>) (n Int)) (!
  (=>
    (<= 0 n)
    (ite
      (<= n (Seq_length s))
      (= (Seq_length (Seq_drop s n)) (- (Seq_length s) n))
      (= (Seq_length (Seq_drop s n)) 0)))
  :pattern ((Seq_length (Seq_drop s n)))
  :qid |$Seq[TYPENAME]_prog.seq_length_over_drop|)))
(assert (forall ((s Seq<TYPENAME>) (n Int) (i Int)) (!
  (=>
    (and (<= 0 n) (and (<= 0 i) (< i (- (Seq_length s) n))))
    (= (Seq_index (Seq_drop s n) i) (Seq_index s (+ i n))))
  :pattern ((Seq_index (Seq_drop s n) i))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_drop_1|)))
(assert (forall ((s Seq<TYPENAME>) (n Int) (i Int)) (!
  (=>
    (and (<= 0 n) (and (<= n i) (< i (Seq_length s))))
    (= (Seq_index (Seq_drop s n) (- i n)) (Seq_index s i)))
  :pattern ((Seq_index s i) (Seq_drop s n))
  :qid |$Seq[TYPENAME]_prog.seq_index_over_drop_2|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME) (n Int)) (!
  (=>
    (and (<= 0 i) (and (< i n) (< n (Seq_length s))))
    (= (Seq_take (Seq_update s i e) n) (Seq_update (Seq_take s n) i e)))
  :pattern ((Seq_take (Seq_update s i e) n))
  :qid |$Seq[TYPENAME]_prog.seq_take_over_update_1|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME) (n Int)) (!
  (=>
    (and (<= n i) (< i (Seq_length s)))
    (= (Seq_take (Seq_update s i e) n) (Seq_take s n)))
  :pattern ((Seq_take (Seq_update s i e) n))
  :qid |$Seq[TYPENAME]_prog.seq_take_over_update_2|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME) (n Int)) (!
  (=>
    (and (<= 0 n) (and (<= n i) (< i (Seq_length s))))
    (= (Seq_drop (Seq_update s i e) n) (Seq_update (Seq_drop s n) (- i n) e)))
  :pattern ((Seq_drop (Seq_update s i e) n))
  :qid |$Seq[TYPENAME]_prog.seq_drop_over_update_1|)))
(assert (forall ((s Seq<TYPENAME>) (i Int) (e TYPENAME) (n Int)) (!
  (=>
    (and (<= 0 i) (and (< i n) (< n (Seq_length s))))
    (= (Seq_drop (Seq_update s i e) n) (Seq_drop s n)))
  :pattern ((Seq_drop (Seq_update s i e) n))
  :qid |$Seq[TYPENAME]_prog.seq_drop_over_update_2|)))
(assert (forall ((s Seq<TYPENAME>) (e TYPENAME) (n Int)) (!
  (=>
    (and (<= 0 n) (<= n (Seq_length s)))
    (= (Seq_drop (Seq_build s e) n) (Seq_build (Seq_drop s n) e)))
  :pattern ((Seq_drop (Seq_build s e) n))
  :qid |$Seq[TYPENAME]_prog.seq_drop_over_build|)))