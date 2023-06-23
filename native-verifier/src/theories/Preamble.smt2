; ===== Static preamble =====

(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-option :tlimit-per 10000)
(set-option :produce-models true) ; equivalent to model.v2 in Z3
(set-option :produce-assignments false) ; similar to model.partial in Z3

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