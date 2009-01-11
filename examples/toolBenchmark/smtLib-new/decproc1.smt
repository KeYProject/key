( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_int_1_2 Int ) (type_of_jint_7_8 Int ) (type_of_jint_Array_4_5 Int ) )
:extrafuns ((dummy_jint_Array_14 Int ) (arrayAccess_jint_10 Int Int Int ) (a_6 Int ) (dummy_int_12 Int ) (_dot_length_9 Int Int ) (dummy_jint_13 Int ) )
:assumption (type_of_jint_Array_4_5 dummy_jint_Array_14)
:assumption (forall (?tvar_15 Int) (forall (?tvar_16 Int) (implies (and (type_of_jint_Array_4_5 ?tvar_15) (type_of_int_1_2 ?tvar_16)) (type_of_jint_7_8 (arrayAccess_jint_10 ?tvar_15 ?tvar_16)))))
:assumption (type_of_jint_Array_4_5 a_6)
:assumption (type_of_int_1_2 dummy_int_12)
:assumption (forall (?tvar_17 Int) (implies (type_of_jint_Array_4_5 ?tvar_17) (type_of_jint_7_8 (_dot_length_9 ?tvar_17))))
:assumption (type_of_jint_7_8 dummy_jint_13)
:assumption (type_of_int_1_2 0)
:assumption (type_of_int_1_2 1)
:assumption (forall (?tvar_18 Int) (implies (type_of_jint_7_8 ?tvar_18) (type_of_int_1_2 ?tvar_18)))
:assumption (forall (?tvar1_20 Int) (forall (?tvar0_19 Int) (implies (and (type_of_int_1_2 ?tvar0_19) (type_of_int_1_2 ?tvar1_20)) (type_of_int_1_2 (- ?tvar0_19 ?tvar1_20)))))
:formula (not (implies true (implies (forall (?x_0 Int) (implies (type_of_int_1_2 ?x_0) (forall (?y_3 Int) (implies (type_of_int_1_2 ?y_3) (implies (and (and (<= 0 ?x_0) (<= ?x_0 ?y_3)) (< ?y_3 (_dot_length_9 a_6))) (<= (arrayAccess_jint_10 a_6 ?x_0) (arrayAccess_jint_10 a_6 ?y_3))))))) (forall (?x_11 Int) (implies (type_of_int_1_2 ?x_11) (implies (and (< 0 ?x_11) (< ?x_11 (_dot_length_9 a_6))) (<= (arrayAccess_jint_10 a_6 (- ?x_11 1)) (arrayAccess_jint_10 a_6 ?x_11))))))))
)