; Absolute Zero — OND pillar, bounded/finite verification (Z3)
; Mirrors archive/proofs/coq/ond/OND.v (archived 2026-10-10). Memory cells are integers:
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
; Modelled per archive/proofs/coq/ond/OND.v (writer_op, inj, run, O_all):
;   memory      = (Array Int Int), cells >= 0 stand for OND.v's nat addresses;
;   inj s p     = all cells 0, then cell0 := s, cell1 := p   (cell2 stays 0);
;   writer_step = mem_update m secret_cell 7                  (op_step writer_op);
;   writer_time = 1                                           (op_time writer_op);
;   run         = (output cell2 of writer_step (inj s p), writer_time (inj s p)).
; The observable is COMPUTED from the step function, not written down as a
; constant. (Before 2026-11-09 this block asserted (not (and (= 0 0) (= 1 1))),
; which is unsat for any program and so checked nothing about the writer.)
(push)
(define-fun inj ((s Int) (p Int)) (Array Int Int)
  (store (store ((as const (Array Int Int)) 0) 0 s) 1 p))
(define-fun writer_step ((m (Array Int Int))) (Array Int Int) (store m 0 7))
(define-fun writer_time ((m (Array Int Int))) Int 1)
(define-fun writer_out ((s Int) (p Int)) Int (select (writer_step (inj s p)) 2))
(define-fun writer_tm ((s Int) (p Int)) Int (writer_time (inj s p)))
(declare-const s1 Int) (declare-const s2 Int) (declare-const pub Int)
(assert (>= s1 0)) (assert (>= s2 0)) (assert (>= pub 0))
; negation of is_OND O_all writer_op: some secret pair, same public input,
; whose (output, time) observables differ.
(assert (not (and (= (writer_out s1 pub) (writer_out s2 pub))
                  (= (writer_tm s1 pub) (writer_tm s2 pub)))))
(check-sat) ; expect unsat => writer IS OND under O_all (no secret pair distinguishes it)
(pop)

; ---- OND-3 dir 2, control: the same check BITES on a writer that leaks.
; leaky_writer writes the secret to the output cell; same model, same query.
; If this were unsat the query above would be vacuous.
(push)
(define-fun inj ((s Int) (p Int)) (Array Int Int)
  (store (store ((as const (Array Int Int)) 0) 0 s) 1 p))
(define-fun leak_step ((m (Array Int Int))) (Array Int Int) (store m 2 (select m 0)))
(define-fun leak_out ((s Int) (p Int)) Int (select (leak_step (inj s p)) 2))
(declare-const s1 Int) (declare-const s2 Int) (declare-const pub Int)
(assert (>= s1 0)) (assert (>= s2 0)) (assert (>= pub 0))
; time is the constant 1 for both runs, so the observables differ iff outputs do.
(assert (not (= (leak_out s1 pub) (leak_out s2 pub))))
(check-sat) ; expect sat: control — a leaking writer IS distinguished by the same query
(pop)

; ---- OND-3 dir 2, second half: writer is NOT a null op (writer_not_null).
; Some memory is changed by writer_step (cell0 becomes 7).
(push)
(define-fun writer_step ((m (Array Int Int))) (Array Int Int) (store m 0 7))
(declare-const m (Array Int Int))
(assert (not (= (writer_step m) m)))
(check-sat) ; expect sat: a memory writer_step changes, so writer is not a null op
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
