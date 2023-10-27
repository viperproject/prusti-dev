; ===== Static preamble =====

(set-info :smt-lib-version 2.6)

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

(set-option :timeout 10000)

; --- Modelling Rust's implementation of % ---

(define-fun rust_mod ((dividend Int) (divisor Int)) Int
  (ite (>= dividend 0)
    (mod dividend (abs divisor))
    (- (mod (- dividend) (abs divisor)))
  )
)

; --- Inequality operator for FloatingPoint bit-vectors ---

(define-fun fp.neq32 ((x (_ FloatingPoint 8 24)) (y (_ FloatingPoint 8 24))) Bool (not (fp.eq x y)))
(define-fun fp.neq64 ((x (_ FloatingPoint 11 53)) (y (_ FloatingPoint 11 53))) Bool (not (fp.eq x y)))

; --- Legacy permission sort ---

(define-sort $Perm () Real)

; ===== End static preamble =====