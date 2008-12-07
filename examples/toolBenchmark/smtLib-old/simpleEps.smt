(benchmark SmtAuflia_2008_To_12_To_05_15h57m08s :status unknown
 :logic AUFLIA
 :extrapreds ((is_int Int))
 :extrapreds ((Func_A_UIP ))
 :extrapreds ((Func_P_UIP Int))
 :formula (not (implies true (or (forall (?LogVar_x_0_int Int) (implies (is_int ?LogVar_x_0_int) (implies Func_A_UIP (Func_P_UIP ?LogVar_x_0_int)))) (forall (?LogVar_x_1_int Int) (implies (is_int ?LogVar_x_1_int) (implies (Func_P_UIP ?LogVar_x_1_int) Func_A_UIP))))))
)