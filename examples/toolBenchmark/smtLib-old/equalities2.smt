(benchmark SmtAuflia_2008_To_12_To_05_15h51m11s :status unknown
 :logic AUFLIA
 :extrafuns ((Func_a_UIF_int Int))
 :extrafuns ((Func_b_UIF_int Int))
 :extrafuns ((Func_non_linear_mult_UIF_int Int Int Int))
 :formula (not (implies true (implies (and (= 5 Func_a_UIF_int) (= 15 (+ Func_b_UIF_int (~ 3)))) (= (Func_non_linear_mult_UIF_int Func_a_UIF_int Func_b_UIF_int) 90))))
)