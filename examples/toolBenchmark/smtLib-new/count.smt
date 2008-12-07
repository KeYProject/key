( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_3 Int ) (type_of_int_1_2 Int ) )
:extrafuns ()
:formula (not (implies (and true (and (and (type_of_int_1_2 1) (and (type_of_int_1_2 0) (and (type_of_int_1_2 2) true))) true)) (implies (and (forall (?x_0 Int) (implies (type_of_int_1_2 ?x_0) (implies (p_3 ?x_0) (p_3 (+ ?x_0 1))))) (p_3 0)) (p_3 2))))
)
