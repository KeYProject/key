( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_s_1_2 Int ) )
:extrafuns ((b_5 Int ) (a_4 Int ) (f_3 Int Int ) )
:formula (not (implies (and true (and (and (forall (?tvar_6 Int) (implies (type_of_s_1_2 ?tvar_6) (type_of_s_1_2 (f_3 ?tvar_6)))) (and (type_of_s_1_2 a_4) (and (type_of_s_1_2 b_5) true))) true)) (implies (and (forall (?x_0 Int) (implies (type_of_s_1_2 ?x_0) (= ?x_0 (f_3 ?x_0)))) (= a_4 b_5)) (= (f_3 (f_3 (f_3 (f_3 a_4)))) b_5))))
)
