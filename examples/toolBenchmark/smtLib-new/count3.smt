( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_s_1_2 Int ) )
:extrafuns ((f_4 Int Int ) (z_6 Int ) (a_5 Int ) (g_3 Int Int ) )
:formula (not (implies (and true (and (and (forall (?tvar_8 Int) (implies (type_of_s_1_2 ?tvar_8) (type_of_s_1_2 (g_3 ?tvar_8)))) (and (type_of_s_1_2 a_5) (and (type_of_s_1_2 z_6) (and (forall (?tvar_7 Int) (implies (type_of_s_1_2 ?tvar_7) (type_of_s_1_2 (f_4 ?tvar_7)))) true)))) true)) (implies (and (forall (?x_0 Int) (implies (type_of_s_1_2 ?x_0) (= (g_3 ?x_0) (f_4 (g_3 ?x_0))))) (= (g_3 (g_3 a_5)) z_6)) (= (f_4 (g_3 (f_4 (g_3 a_5)))) z_6))))
)
