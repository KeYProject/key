( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_s_1_2 Int ) )
:extrafuns ((b_5 Int ) (f_3 Int Int ) (a_4 Int ) (dummy_s_6 Int ) )
:assumption (type_of_s_1_2 b_5)
:assumption (forall (?tvar_7 Int) (implies (type_of_s_1_2 ?tvar_7) (type_of_s_1_2 (f_3 ?tvar_7))))
:assumption (type_of_s_1_2 a_4)
:assumption (type_of_s_1_2 dummy_s_6)
:formula (not (implies true (implies (and (forall (?x_0 Int) (implies (type_of_s_1_2 ?x_0) (= ?x_0 (f_3 ?x_0)))) (= a_4 b_5)) (= (f_3 (f_3 (f_3 (f_3 a_4)))) b_5))))
)
