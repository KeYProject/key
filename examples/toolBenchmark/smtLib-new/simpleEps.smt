( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((P_4 Int ) (A_3 ) (type_of_int_1_2 Int ) )
:extrafuns ((dummy_int_6 Int ) )
:assumption (type_of_int_1_2 dummy_int_6)
:formula (not (implies true (or (forall (?x_0 Int) (implies (type_of_int_1_2 ?x_0) (implies A_3 (P_4 ?x_0)))) (forall (?x_5 Int) (implies (type_of_int_1_2 ?x_5) (implies (P_4 ?x_5) A_3))))))
)