; ===== Static preamble =====

(set-logic ALL)
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