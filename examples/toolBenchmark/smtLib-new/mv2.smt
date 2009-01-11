( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_3 Int ) (type_of_S_1_2 Int ) )
:extrafuns ((a_4 Int ) (dummy_S_5 Int ) )
:assumption (type_of_S_1_2 a_4)
:assumption (type_of_S_1_2 dummy_S_5)
:formula (not (implies true (implies (and (forall (?x_0 Int) (implies (type_of_S_1_2 ?x_0) (p_3 ?x_0))) (not (p_3 a_4))) false)))
)