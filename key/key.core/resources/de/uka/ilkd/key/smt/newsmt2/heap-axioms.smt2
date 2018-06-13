(define-sort sort_Heap () (Array U U U))

(declare-fun u2h (U) sort_Heap)
(declare-fun h2u (sort_Heap) U)
(assert (forall ((h sort_Heap)) (= (u2h (h2u h)) h)))

(declare-fun wellFormed (sort_Heap) Bool)

(declare-const field_created U)

(declare-fun keystore (sort_Heap U U U) sort_Heap)
(assert (forall ((h sort_Heap) (o U) (f U) (v U)) (ite (= f field_created) 
		(= h (keystore h o f v)) 
		(= (store h o f v) (keystore h o f v)))))

; (declare-fun keyselect (sort_Heap U U) U)
; (assert (forall ((h sort_Heap) (u2 U) (u3 U)) (subtype (typeof (keyselect h u2 u3)) sort_any)))

; (assert (forall ((h sort_Heap) (o1 U) (f1 U) (v U) (o2 U) (f2 U)) (ite (= f1 field_created)
; 		(= (keyselect (store h o1 f1 v) o2 f2) f1)
; 		(ite (and (= o1 o2) (= f1 f2)) (= (keyselect (store h o1 f1 v) o2 f2) v) (= (keyselect (store h o1 f1 v) o2 f2) (select h o2 f2))))))