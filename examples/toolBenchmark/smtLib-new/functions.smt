( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_s_1_2 Int ) )
:extrafuns ((dummy_s_7 Int ) (a_5 Int ) (g_3 Int Int ) (f_4 Int Int ) (b_6 Int ) )
:assumption (type_of_s_1_2 dummy_s_7)
:assumption (type_of_s_1_2 a_5)
:assumption (forall (?tvar_8 Int) (implies (type_of_s_1_2 ?tvar_8) (type_of_s_1_2 (g_3 ?tvar_8))))
:assumption (forall (?tvar_9 Int) (implies (type_of_s_1_2 ?tvar_9) (type_of_s_1_2 (f_4 ?tvar_9))))
:assumption (type_of_s_1_2 b_6)
:formula (not (implies true (implies (and (forall (?x_0 Int) (implies (type_of_s_1_2 ?x_0) (= (f_4 (g_3 ?x_0)) (g_3 ?x_0)))) (= (g_3 a_5) b_6)) (= (f_4 b_6) (g_3 a_5)))))
)