(set-option :print-success true) 

(set-option :produce-unsat-cores true)

(set-option :produce-models true)

(declare-sort T 0)
(declare-sort U 0)
(define-sort sort_heap () (Array U U U))
(declare-const sort_any T)
(declare-const null U)

(declare-fun u2i (U) Int)
(declare-fun i2u (Int) U)
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))

(declare-fun u2b (U) Bool)
(declare-fun b2u (Bool) U)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))

(declare-fun subtype (T T) Bool)

(assert (forall ((t1 T)) (subtype t1 t1)))
(assert (forall ((t1 T) (t2 T)) (! (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2)) :pattern ((subtype t1 t2) (subtype t2 t1)))))
(assert (forall ((t1 T) (t2 T) (t3 T)) (! (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3)) :pattern ((subtype t1 t2) (subtype t2 t3)))))

(declare-fun typeof (U) T)

(declare-fun cast (U T) U)
(assert (forall ((x U) (t T)) (! (subtype (typeof (cast x t)) t) :pattern (cast x t)))) 				
(assert (forall ((x U) (t T)) (! (=> (subtype (typeof x) t) (= (cast x t) x)) :pattern (cast x t))))

(declare-fun instanceof (U T) Bool)
(assert (forall ((u U) (t T)) (=> (instanceof u t) (subtype (typeof u) t))))

(declare-fun exactinstanceof (U T) Bool)
(assert (forall ((u U) (t T)) (=> (exactinstanceof u t) (= (typeof u) t))))

(declare-fun wellFormed (sort_heap) Bool)

(declare-const field_created U)
(declare-fun keystore (sort_heap U U U) sort_heap)
(assert (forall ((h sort_heap) (o U) (f U) (v U)) (ite (= f field_created) 
		(= h (keystore h o f v)) 
		(= (store h o f v) (keystore h o f v)))))

; (declare-fun keyselect (sort_heap U U) U)
; (assert (forall ((h sort_heap) (u2 U) (u3 U)) (subtype (typeof (keyselect h u2 u3)) sort_any)))

; (assert (forall ((h sort_heap) (o1 U) (f1 U) (v U) (o2 U) (f2 U)) (ite (= f1 field_created)
; 		(= (keyselect (store h o1 f1 v) o2 f2) f1)
; 		(ite (and (= o1 o2) (= f1 f2)) (= (keyselect (store h o1 f1 v) o2 f2) v) (= (keyselect (store h o1 f1 v) o2 f2) (select h o2 f2))))))
