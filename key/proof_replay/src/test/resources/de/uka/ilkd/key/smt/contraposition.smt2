Result: valid

unsat
((set-logic ALL)
(proof
(let (($x213 (not KeY_p)))
(let (($x214 (or KeY_q $x213)))
(let (($x224 (not $x214)))
(let ((@x222 (mp
                (asserted (not (=> (not KeY_q) $x213)))
                (rewrite (= (not (=> (not KeY_q) $x213)) $x224))
                $x224
              )))
(let ((@x226 (not-or-elim @x222 KeY_p)))
(let ((@x234 (monotonicity
                (iff-true @x226 (= KeY_p true))
                (= $x213 (not true))
              )))
(let ((@x241 (monotonicity
                (iff-false
                    (not-or-elim @x222 (not KeY_q))
                    (= KeY_q false)
                )
                (trans
                    @x234
                    (rewrite (= (not true) false))
                    (= $x213 false)
                )
                (= $x214 (or false false))
              )))
(let ((@x245 (trans
                @x241
                (rewrite (= (or false false) false))
                (= $x214 false)
              )))
(let ((@x217 (mp (asserted (=> KeY_p KeY_q)) (rewrite (= (=> KeY_p KeY_q) $x214)) $x214)))
(mp @x217 @x245 false))))))))))))
