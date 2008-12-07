( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_jint_Array_4_5 Int ) (type_of_jint_7_8 Int ) (type_of_int_1_2 Int ) )
:extrafuns ((a_6 Int ) (arrayAccess_jint_10 Int Int Int ) (_dot_length_9 Int Int ) )
:formula (not (implies (and (and true (forall (?tvar_15 Int) (implies (type_of_jint_7_8 ?tvar_15) (type_of_int_1_2 ?tvar_15)))) (and (and (type_of_int_1_2 1) (and (type_of_int_1_2 0) (and (forall (?tvar_14 Int) (implies (type_of_jint_Array_4_5 ?tvar_14) (type_of_jint_7_8 (_dot_length_9 ?tvar_14)))) (and (forall (?tvar_12 Int) (forall (?tvar_13 Int) (implies (and (type_of_jint_Array_4_5 ?tvar_12) (type_of_int_1_2 ?tvar_13)) (type_of_jint_7_8 (arrayAccess_jint_10 ?tvar_12 ?tvar_13))))) (and (type_of_jint_Array_4_5 a_6) true))))) true)) (implies (forall (?x_0 Int) (implies (type_of_int_1_2 ?x_0) (forall (?y_3 Int) (implies (type_of_int_1_2 ?y_3) (implies (and (and (<= 0 ?x_0) (<= ?x_0 ?y_3)) (< ?y_3 (_dot_length_9 a_6))) (<= (arrayAccess_jint_10 a_6 ?x_0) (arrayAccess_jint_10 a_6 ?y_3))))))) (forall (?x_11 Int) (implies (type_of_int_1_2 ?x_11) (implies (and (< 0 ?x_11) (< ?x_11 (_dot_length_9 a_6))) (<= (arrayAccess_jint_10 a_6 (- ?x_11 1)) (arrayAccess_jint_10 a_6 ?x_11))))))))
)
