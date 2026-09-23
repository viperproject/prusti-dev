; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $PRD$ is a Silver predicate name
;   - $S$ is the sort corresponding to the type of the field

; PRUSTI OVERRIDE: Silicon's extensionality axiom for predicate snapshot
; functions (qid qp.$PSF<$PRD$>-eq-outer) is omitted. It is triggered by
; every PAIR of snapshot functions of heap-dependent function applications
; with quantified preconditions, and each instance is a case split between
; "the domains are equal" and a skolem witness of their difference, which
; then instantiates the inverse-function and permission axioms of every
; quantified chunk. With the interior-mutability value maps (im0_snap etc.)
; this made single permission checks take minutes. The encoding does not
; rely on the axiom: value maps of different evaluations are related
; pointwise (im_map_restrict canonicity, function definitions).

(assert (forall ((s $Snap) (pm $PPM)) (!
    ($Perm.isValidVar ($PSF.perm_$PRD$ pm s))
    :pattern (($PSF.perm_$PRD$ pm s))
    :qid |qp.$PSF<$PRD$>-validvar|)))

(assert (forall ((s $Snap) (f $S$)) (!
    (= ($PSF.loc_$PRD$ f s) true)
    :pattern (($PSF.loc_$PRD$ f s))
    :qid |qp.$PSF<$PRD$>-loc|)))
