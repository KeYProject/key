(declare-sort T 0)
(declare-sort u 0)

(declare-fun u2i (u) Int)
(declare-fun i2u (Int) u)
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))

(declare-fun u2b (u) Bool)
(declare-fun b2u (Bool) u)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))

(declare-fun subtype (T T) Bool)

(assert (forall ((t1 T)) (subtype t1 t1)))
(assert (forall ((t1 T) (t2 T)) (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2))))
(assert (forall ((t1 T) (t2 T) (t3 T)) (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3))))

(declare-fun typeof (u) T)

(declare-fun cast (T u) u)
(assert (forall ((t T) (x u)) (subtype (typeof x) t)))
(assert (forall ((t T) (x u)) (subtype (typeof (cast (t x))) t))) 				; TODO, das kompiliert nicht
(assert (forall ((t T) (x u)) (=> (subtype (typeof x) t) (= (cast (t x) x)))))	; TODO, das kompiliert nicht