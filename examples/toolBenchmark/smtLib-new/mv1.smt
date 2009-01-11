( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_3 Int ) (type_of_S_1_2 Int ) )
:extrafuns ((dummy_S_5 Int ) (a_4 Int ) )
:assumption (type_of_S_1_2 dummy_S_5)
:assumption (type_of_S_1_2 a_4)
:formula (not (implies true (implies (forall (?x_0 Int) (implies (type_of_S_1_2 ?x_0) (p_3 ?x_0))) (p_3 a_4))))
)