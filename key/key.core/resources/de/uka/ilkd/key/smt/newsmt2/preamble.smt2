(declare-sort T 0)
(declare-sort u 0)

(declare-fun u2i (u) Int)
(declare-fun i2u (Int) u)
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))

(declare-fun u2b (u) Bool)
(declare-fun b2u (Bool) u)
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))

(declare-fun subtype (T T) Bool)
(declare-const t1 T)
(declare-const t2 T)
(declare-const t3 T)
(assert (subtype t1 t1))
(assert (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3)))
(assert (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2)))
