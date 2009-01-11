( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_3 Int ) (type_of_int_1_2 Int ) )
:extrafuns ((dummy_int_4 Int ) )
:assumption (type_of_int_1_2 dummy_int_4)
:assumption (type_of_int_1_2 0)
:assumption (type_of_int_1_2 2)
:assumption (type_of_int_1_2 1)
:assumption (forall (?tvar1_6 Int) (forall (?tvar0_5 Int) (implies (and (type_of_int_1_2 ?tvar0_5) (type_of_int_1_2 ?tvar1_6)) (type_of_int_1_2 (+ ?tvar0_5 ?tvar1_6)))))
:formula (not (implies true (implies (and (forall (?x_0 Int) (implies (type_of_int_1_2 ?x_0) (implies (p_3 ?x_0) (p_3 (+ ?x_0 1))))) (p_3 0)) (p_3 2))))
)
