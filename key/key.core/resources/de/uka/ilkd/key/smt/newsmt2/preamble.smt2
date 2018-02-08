(declare-function u2i (u) Int)
(declare-function i2u (Int) u)
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))

(declare-function u2b (u) Bool)
(declare-function b2u (Bool) u)
(assert (forall ((b Bool)) (= (u2b (i2u b)) b)))

