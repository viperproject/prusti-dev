; ===== Static preamble =====

(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :type_check true)
(set-option :smt.bv.reflect true)
(set-option :smt.mbqi false)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :smt.qi.eager_threshold 1000)
(set-option :smt.qi.max_multi_patterns 1000)
(set-option :smt.phase_selection 0) ; default: 3, Boogie: 0
(set-option :sat.phase caching)
(set-option :sat.random_seed 0)
(set-option :nlsat.randomize true)
(set-option :nlsat.seed 0)
(set-option :nlsat.shuffle_vars false)
(set-option :fp.spacer.order_children 0) ; Not available with Z3 4.5
(set-option :fp.spacer.random_seed 0) ; Not available with Z3 4.5
(set-option :smt.arith.random_initial_value true) ; Boogie: true
(set-option :smt.random_seed 0)
(set-option :sls.random_offset true)
(set-option :sls.random_seed 0)
(set-option :sls.restart_init false)
(set-option :sls.walksat_ucb true)
(set-option :model.v2 true)
(set-option :model.partial false)

(set-option :timeout 1000)

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