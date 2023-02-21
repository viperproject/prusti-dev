
; ===== Set theory for type TYPENAME =====

(declare-sort Set<TYPENAME> 0)

(declare-fun Set_in (TYPENAME Set<TYPENAME>) Bool)
(declare-fun Set_card (Set<TYPENAME>) Int)
(declare-const Set_empty Set<TYPENAME>)
(declare-fun Set_singleton (TYPENAME) Set<TYPENAME>)
(declare-fun Set_unionone (Set<TYPENAME> TYPENAME) Set<TYPENAME>)
(declare-fun Set_union (Set<TYPENAME> Set<TYPENAME>) Set<TYPENAME>)
(declare-fun Set_disjoint (Set<TYPENAME> Set<TYPENAME>) Bool)
(declare-fun Set_difference (Set<TYPENAME> Set<TYPENAME>) Set<TYPENAME>)
(declare-fun Set_intersection (Set<TYPENAME> Set<TYPENAME>) Set<TYPENAME>)
(declare-fun Set_subset (Set<TYPENAME> Set<TYPENAME>) Bool)
(declare-fun Set_equal (Set<TYPENAME> Set<TYPENAME>) Bool)

(assert (forall ((s Set<TYPENAME>)) (!
    (<= 0 (Set_card s))
    :pattern ((Set_card s))
    :qid |$Set[TYPENAME]_prog.card_non_negative|)))
(assert (forall ((e TYPENAME)) (!
    (not (Set_in e (as Set_empty  Set<TYPENAME>)))
    :pattern ((Set_in e (as Set_empty  Set<TYPENAME>)))
    :qid |$Set[TYPENAME]_prog.in_empty_set|)))
(assert (forall ((s Set<TYPENAME>)) (!
    (and
    (= (= (Set_card s) 0) (= s (as Set_empty  Set<TYPENAME>)))
    (=>
        (not (= (Set_card s) 0))
        (exists ((e TYPENAME)) (!
        (Set_in e s)
        :pattern ((Set_in e s))
        ))))
    :pattern ((Set_card s))
    :qid |$Set[TYPENAME]_prog.empty_set_cardinality|)))
(assert (forall ((e TYPENAME)) (!
    (Set_in e (Set_singleton e))
    :pattern ((Set_singleton e))
    :qid |$Set[TYPENAME]_prog.in_singleton_set|)))
(assert (forall ((e1 TYPENAME) (e2 TYPENAME)) (!
    (= (Set_in e1 (Set_singleton e2)) (= e1 e2))
    :pattern ((Set_in e1 (Set_singleton e2)))
    :qid |$Set[TYPENAME]_prog.in_singleton_set_equality|)))
(assert (forall ((e TYPENAME)) (!
    (= (Set_card (Set_singleton e)) 1)
    :pattern ((Set_card (Set_singleton e)))
    :qid |$Set[TYPENAME]_prog.singleton_set_cardinality|)))
(assert (forall ((s Set<TYPENAME>) (e TYPENAME)) (!
    (Set_in e (Set_unionone s e))
    :pattern ((Set_unionone s e))
    :qid |$Set[TYPENAME]_prog.in_unionone_same|)))
(assert (forall ((s Set<TYPENAME>) (e1 TYPENAME) (e2 TYPENAME)) (!
    (= (Set_in e1 (Set_unionone s e2)) (or (= e1 e2) (Set_in e1 s)))
    :pattern ((Set_in e1 (Set_unionone s e2)))
    :qid |$Set[TYPENAME]_prog.in_unionone_other|)))
(assert (forall ((s Set<TYPENAME>) (e1 TYPENAME) (e2 TYPENAME)) (!
    (=> (Set_in e1 s) (Set_in e1 (Set_unionone s e2)))
    :pattern ((Set_in e1 s) (Set_unionone s e2))
    :qid |$Set[TYPENAME]_prog.invariance_in_unionone|)))
(assert (forall ((s Set<TYPENAME>) (e TYPENAME)) (!
    (=> (Set_in e s) (= (Set_card (Set_unionone s e)) (Set_card s)))
    :pattern ((Set_card (Set_unionone s e)))
    :qid |$Set[TYPENAME]_prog.unionone_cardinality_invariant|)))
(assert (forall ((s Set<TYPENAME>) (e TYPENAME)) (!
    (=> (not (Set_in e s)) (= (Set_card (Set_unionone s e)) (+ (Set_card s) 1)))
    :pattern ((Set_card (Set_unionone s e)))
    :qid |$Set[TYPENAME]_prog.unionone_cardinality_changed|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (= (Set_in e (Set_union s1 s2)) (or (Set_in e s1) (Set_in e s2)))
    :pattern ((Set_in e (Set_union s1 s2)))
    :qid |$Set[TYPENAME]_prog.in_union_in_one|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (=> (Set_in e s1) (Set_in e (Set_union s1 s2)))
    :pattern ((Set_in e s1) (Set_union s1 s2))
    :qid |$Set[TYPENAME]_prog.in_left_in_union|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (=> (Set_in e s2) (Set_in e (Set_union s1 s2)))
    :pattern ((Set_in e s2) (Set_union s1 s2))
    :qid |$Set[TYPENAME]_prog.in_right_in_union|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (= (Set_in e (Set_intersection s1 s2)) (and (Set_in e s1) (Set_in e s2)))
    :pattern ((Set_in e (Set_intersection s1 s2)))
    :pattern ((Set_intersection s1 s2) (Set_in e s1))
    :pattern ((Set_intersection s1 s2) (Set_in e s2))
    :qid |$Set[TYPENAME]_prog.in_intersection_in_both|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (= (Set_union s1 (Set_union s1 s2)) (Set_union s1 s2))
    :pattern ((Set_union s1 (Set_union s1 s2)))
    :qid |$Set[TYPENAME]_prog.union_left_idempotency|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (= (Set_union (Set_union s1 s2) s2) (Set_union s1 s2))
    :pattern ((Set_union (Set_union s1 s2) s2))
    :qid |$Set[TYPENAME]_prog.union_right_idempotency|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (= (Set_intersection s1 (Set_intersection s1 s2)) (Set_intersection s1 s2))
    :pattern ((Set_intersection s1 (Set_intersection s1 s2)))
    :qid |$Set[TYPENAME]_prog.intersection_left_idempotency|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (= (Set_intersection (Set_intersection s1 s2) s2) (Set_intersection s1 s2))
    :pattern ((Set_intersection (Set_intersection s1 s2) s2))
    :qid |$Set[TYPENAME]_prog.intersection_right_idempotency|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (=
    (+ (Set_card (Set_union s1 s2)) (Set_card (Set_intersection s1 s2)))
    (+ (Set_card s1) (Set_card s2)))
    :pattern ((Set_card (Set_union s1 s2)))
    :pattern ((Set_card (Set_intersection s1 s2)))
    :qid |$Set[TYPENAME]_prog.cardinality_sums|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (= (Set_in e (Set_difference s1 s2)) (and (Set_in e s1) (not (Set_in e s2))))
    :pattern ((Set_in e (Set_difference s1 s2)))
    :qid |$Set[TYPENAME]_prog.in_difference|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>) (e TYPENAME)) (!
    (=> (Set_in e s2) (not (Set_in e (Set_difference s1 s2))))
    :pattern ((Set_difference s1 s2) (Set_in e s2))
    :qid |$Set[TYPENAME]_prog.not_in_difference|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (=
    (Set_subset s1 s2)
    (forall ((e TYPENAME)) (!
        (=> (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        :pattern ((Set_in e s2))
        )))
    :pattern ((Set_subset s1 s2))
    :qid |$Set[TYPENAME]_prog.subset_definition|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (=
    (Set_equal s1 s2)
    (forall ((e TYPENAME)) (!
        (= (Set_in e s1) (Set_in e s2))
        :pattern ((Set_in e s1))
        :pattern ((Set_in e s2))
        )))
    :pattern ((Set_equal s1 s2))
    :qid |$Set[TYPENAME]_prog.equality_definition|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (=> (Set_equal s1 s2) (= s1 s2))
    :pattern ((Set_equal s1 s2))
    :qid |$Set[TYPENAME]_prog.native_equality|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (=
    (Set_disjoint s1 s2)
    (forall ((e TYPENAME)) (!
        (or (not (Set_in e s1)) (not (Set_in e s2)))
        :pattern ((Set_in e s1))
        :pattern ((Set_in e s2))
        )))
    :pattern ((Set_disjoint s1 s2))
    :qid |$Set[TYPENAME]_prog.disjointness_definition|)))
(assert (forall ((s1 Set<TYPENAME>) (s2 Set<TYPENAME>)) (!
    (and
    (=
        (+
        (+ (Set_card (Set_difference s1 s2)) (Set_card (Set_difference s2 s1)))
        (Set_card (Set_intersection s1 s2)))
        (Set_card (Set_union s1 s2)))
    (=
        (Set_card (Set_difference s1 s2))
        (- (Set_card s1) (Set_card (Set_intersection s1 s2)))))
    :pattern ((Set_card (Set_difference s1 s2)))
    :qid |$Set[TYPENAME]_prog.cardinality_difference|)))
