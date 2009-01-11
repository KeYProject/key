( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_4 Int Int ) (type_of_s_1_2 Int ) )
:extrafuns ((dummy_s_7 Int ) )
:assumption (type_of_s_1_2 dummy_s_7)
:formula (not (implies true (implies (exists(?x_0 Int)(and (type_of_s_1_2 ?x_0) (forall (?y_3 Int) (implies (type_of_s_1_2 ?y_3) (p_4 ?x_0 ?y_3))))) (forall (?v_5 Int) (implies (type_of_s_1_2 ?v_5) (exists(?u_6 Int)(and (type_of_s_1_2 ?u_6) (p_4 ?u_6 ?v_5))))))))
)