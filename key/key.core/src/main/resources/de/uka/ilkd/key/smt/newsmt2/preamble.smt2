; BEGIN preamble from preamble.smt2

(set-option :print-success true)
(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-logic ALL)

(declare-sort T 0)
(declare-sort U 0)

(declare-fun instanceof (U T) Bool)
(declare-fun exactinstanceof (U T) Bool)
(declare-fun subtype (T T) Bool)
(declare-fun typeof (U) T)

(assert (forall ((t1 T)) (subtype t1 t1)))
(assert (forall ((t1 T) (t2 T)) (! (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2)) :pattern ((subtype t1 t2) (subtype t2 t1)))))
(assert (forall ((t1 T) (t2 T) (t3 T)) (! (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3)) :pattern ((subtype t1 t2) (subtype t2 t3)))))
(assert (forall ((u U) (t T)) (! (= (instanceof u t) (subtype (typeof u) t)) :pattern ((instanceof u t)))))
(assert (forall ((u U) (t T)) (! (= (exactinstanceof u t) (= (typeof u) t)) :pattern ((exactinstanceof u t)))))

; END preamble from preamble.smt2

