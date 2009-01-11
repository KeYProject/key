( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((p_4 Int Int ) (type_of_s_1_2 Int ) )
:extrafuns ((dummy_s_5 Int ) )
:assumption (type_of_s_1_2 dummy_s_5)
:formula (not (implies true (exists(?x_0 Int)(and (type_of_s_1_2 ?x_0) (exists(?y_3 Int)(and (type_of_s_1_2 ?y_3) (and (implies (p_4 ?x_0 ?y_3) (p_4 ?y_3 ?x_0)) (implies (p_4 ?y_3 ?x_0) (p_4 ?x_0 ?y_3)))))))))
)