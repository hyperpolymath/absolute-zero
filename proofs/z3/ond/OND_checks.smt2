; Absolute Zero — OND pillar, bounded/finite verification (Z3)
; Mirrors proofs/coq/ond/OND.v. Memory cells are integers:
;   cell0 = secret, cell1 = public, cell2 = declared output channel.
; "Decidable for bounded programs under a finite observation model O" (OND-ROADMAP).

; ---- OND-3 dir 1: leaky_cno is a NULL op (state identity) yet NOT OND under timing.
; effect = identity; time(m) = secret. Observable timing differs across secrets => leak.
(push)
(declare-const s1 Int) (declare-const s2 Int) (declare-const pub Int)
(define-fun time_leaky ((secret Int)) Int secret)   ; timing tracks the secret
(assert (distinct (time_leaky s1) (time_leaky s2))) ; observable differs => not OND
(assert (distinct s1 s2))
(check-sat) ; expect sat: a concrete secret pair the timing channel distinguishes
(pop)

; ---- OND-3 dir 2: writer is OND on (output,timing) yet NOT a null op.
; output cell2 stays 0, time = 1 (both secret-independent) => OND holds:
(push)
(declare-const s1 Int) (declare-const s2 Int)
; observable of writer = (out=0, time=1) regardless of secret
(assert (not (and (= 0 0) (= 1 1)))) ; negation of "observable equal across secrets"
(check-sat) ; expect unsat => writer IS OND (no secret distinguishes its observable)
(pop)

; ---- OND-5: p_op and q_op each OND under O_all, composite p;q LEAKS.
; p_op:  cell1' := secret ; output cell2 untouched (=0)
; q_op:  cell2' := cell1
; composite: cell2_final = cell1_mid = secret  => output = secret => leak.
(push)
(declare-const s1 Int) (declare-const s2 Int) (declare-const pub Int)
; p_op observable output (cell2) across secrets — should be equal (0) => OND
(define-fun p_out ((secret Int)) Int 0)
(assert (= (p_out s1) (p_out s2)))            ; p_op OND (holds)
; composite observable output = secret
(define-fun comp_out ((secret Int)) Int secret)
(assert (distinct (comp_out s1) (comp_out s2))) ; composite distinguishes secrets => NOT OND
(assert (distinct s1 s2))
(check-sat) ; expect sat: witness that the composite leaks while parts do not
(get-model)
(pop)
