( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_int_0_1 Int ) )
:extrafuns ((dummy_int_4 Int ) (a_2 Int ) (b_3 Int ) )
:assumption (type_of_int_0_1 dummy_int_4)
:assumption (type_of_int_0_1 a_2)
:assumption (type_of_int_0_1 b_3)
:assumption (type_of_int_0_1 65)
:assumption (type_of_int_0_1 3)
:assumption (type_of_int_0_1 5)
:assumption (type_of_int_0_1 15)
:assumption (forall (?tvar1_6 Int) (forall (?tvar0_5 Int) (implies (and (type_of_int_0_1 ?tvar0_5) (type_of_int_0_1 ?tvar1_6)) (type_of_int_0_1 (+ ?tvar0_5 ?tvar1_6)))))
:assumption (forall (?tvar1_8 Int) (forall (?tvar0_7 Int) (implies (and (type_of_int_0_1 ?tvar0_7) (type_of_int_0_1 ?tvar1_8)) (type_of_int_0_1 (* ?tvar0_7 ?tvar1_8)))))
:formula (not (implies true (implies (and (= 5 a_2) (= (+ 15 (+ 3 (- 0 a_2))) b_3)) (= (* a_2 b_3) 65))))
)
