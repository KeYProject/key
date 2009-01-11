( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_S_1_2 Int ) )
:extrafuns ((dummy_S_5 Int ) )
:assumption (type_of_S_1_2 dummy_S_5)
:formula (not (implies true (forall (?x_0 Int) (implies (type_of_S_1_2 ?x_0) (forall (?y_3 Int) (implies (type_of_S_1_2 ?y_3) (and (= ?y_3 ?x_0) (forall (?x_4 Int) (implies (type_of_S_1_2 ?x_4) (= ?y_3 ?x_4))))))))))
)
