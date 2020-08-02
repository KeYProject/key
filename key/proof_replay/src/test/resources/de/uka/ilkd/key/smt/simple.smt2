((declare-fun x!0 () Int)
(proof
(let ((@x56
    (mp~
        (mp
            (asserted
                (exists ((x Int) )(and (> x 0) (< x 0)))
            )
            (quant-intro
                (monotonicity
                    (rewrite (= (> ?0 0) (not (<= ?0 0))))
                    (rewrite (= (< ?0 0) (not (>= ?0 0))))
                    (= (and (> ?0 0) (< ?0 0)) (and (not (<= ?0 0)) (not (>= ?0 0))))
                )
                (=
                    (exists ((x Int) )(and (> x 0) (< x 0)))
                    (exists ((x Int) )(and (not (<= x 0)) (not (>= x 0))))
                )
            )
            (exists ((x Int) )(and (not (<= x 0)) (not (>= x 0))))
        )
        (sk
            (~
                (exists ((x Int) )(and (not (<= x 0)) (not (>= x 0))))
                (and (not (<= x!0 0)) (not (>= x!0 0)))
            )
        )
        (and (not (<= x!0 0)) (not (>= x!0 0)))
    )
))

(unit-resolution
    ((_ th-lemma arith farkas 1 1) (or (>= x!0 0) (<= x!0 0)))
    (and-elim @x56 (not (<= x!0 0)))
    (and-elim @x56 (not (>= x!0 0)))
    false
)
)))
