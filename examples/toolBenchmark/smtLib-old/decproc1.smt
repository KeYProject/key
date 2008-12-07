(benchmark SmtAuflia_2008_To_12_To_05_15h58m36s :status unknown
 :logic AUFLIA
 :extrafuns ((ProgVar_a_0_UIF_object Int))
 :extrafuns ((AttrOp_length_0_UIF_int Int Int))
 :extrafuns ((Array_UIF_int Int Int Int))
 :extrapreds ((is_jint_Array Int))
 :extrapreds ((is_int Int))
 :formula (not (implies (and (and (and (is_jint_Array ProgVar_a_0_UIF_object) (forall (?x_0 Int) (is_int (AttrOp_length_0_UIF_int ?x_0)))) (forall (?x_0 Int) (?x_1 Int) (is_int (Array_UIF_int ?x_0 ?x_1)))) true) (implies (forall (?LogVar_x_0_int Int) (implies (is_int ?LogVar_x_0_int) (forall (?LogVar_y_1_int Int) (implies (is_int ?LogVar_y_1_int) (implies (and (and (<= 0 ?LogVar_x_0_int) (<= ?LogVar_x_0_int ?LogVar_y_1_int)) (< ?LogVar_y_1_int (AttrOp_length_0_UIF_int ProgVar_a_0_UIF_object))) (<= (Array_UIF_int ProgVar_a_0_UIF_object ?LogVar_x_0_int) (Array_UIF_int ProgVar_a_0_UIF_object ?LogVar_y_1_int))))))) (forall (?LogVar_x_2_int Int) (implies (is_int ?LogVar_x_2_int) (implies (and (< 0 ?LogVar_x_2_int) (< ?LogVar_x_2_int (AttrOp_length_0_UIF_int ProgVar_a_0_UIF_object))) (<= (Array_UIF_int ProgVar_a_0_UIF_object (- ?LogVar_x_2_int 1)) (Array_UIF_int ProgVar_a_0_UIF_object ?LogVar_x_2_int))))))))
)
