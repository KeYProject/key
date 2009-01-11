( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_3 Int ) (q_4 Int ) (type_of_int_1_2 Int ) )
:extrafuns ((dummy_int_5 Int ) )
:assumption (type_of_int_1_2 dummy_int_5)
:assumption (type_of_int_1_2 12)
:assumption (type_of_int_1_2 0)
:assumption (type_of_int_1_2 1)
:formula (not (implies true (implies (and (and (forall (?mv0_0 Int) (implies (type_of_int_1_2 ?mv0_0) (implies (p_3 ?mv0_0) (q_4 ?mv0_0)))) (p_3 0)) (p_3 1)) (q_4 12))))
)