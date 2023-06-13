; ===== Static preamble =====

(set-info :smt-lib-version 2.6)

(set-logic ALL)

(set-option :tlimit-per 5000)

(set-option :auto-extend-integers true) ; similar to global-decls in Z3
(set-option :incrementality false) ; similar to auto_config in Z3

; Note: restart_strategy and restart_factor do not have direct equivalents in CVC5. 
; Similar functionality might be achieved through tuning the various options for decision strategies, but there is no one-to-one mapping.

(set-option :bitvector-div-zero-const false) ; similar to smt.bv.reflect in Z3
(set-option :mbqi-mode none) ; similar to smt.mbqi in Z3

; The options smt.qi.cost, smt.qi.eager_threshold, and smt.qi.max_multi_patterns might correspond to 
; configuring quantifier instantiation strategies in CVC5, but there are no direct equivalents.

(set-option :decision-random-frequency 0) ; similar to sat.phase caching in Z3

; There are no direct equivalents in CVC5 for sat.random_seed, nlsat.* options.

; Note: fp.spacer.* options are related to Z3's Spacer, a software model checker. CVC5 doesn't have Spacer.

(set-option :random-seed 0) ; similar to smt.random_seed in Z3

; The sls.* options in Z3 are related to stochastic local search. 
; CVC5 has options for tuning its decision strategy, but these are quite different from SLS and do not directly correspond to these options.

(set-option :produce-models true) ; equivalent to model.v2 in Z3
(set-option :produce-assignments false) ; similar to model.partial in Z3

; --- Floating-point arithmetic ---

(define-fun fp.neq32 ((x (_ FloatingPoint 8 24)) (y (_ FloatingPoint 8 24))) Bool (not (fp.eq x y)))
(define-fun fp.neq64 ((x (_ FloatingPoint 11 53)) (y (_ FloatingPoint 11 53))) Bool (not (fp.eq x y)))

; --- Snapshots ---

(declare-datatypes (($Snap 0)) ((
    ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))

; --- References ---

(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)

; --- Permissions ---

(declare-sort $FPM 0)
(declare-sort $PPM 0)
(define-sort $Perm () Real)

(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)

(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))

(define-fun $Perm.isReadVar ((p $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))))

; min function for permissions
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))

; --- Sort wrappers ---

; Sort wrappers are no longer part of the static preamble. Instead, they are
; emitted as part of the program-specific preamble.

; --- Math ---

;function Math#min(a: int, b: int): int;
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))

;function Math#clip(a: int): int;
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))

; ===== End static preamble =====