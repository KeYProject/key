( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_java_dot_lang_dot_Object_1_2 Int ) (type_of_java_dot_lang_dot_String_Array_3_4 Int ) )
:extrafuns ((oldAr_5 Int ) (null Int ) )
:formula (not (implies (and (and (type_of_java_dot_lang_dot_String_Array_3_4 null) (and (type_of_java_dot_lang_dot_Object_1_2 null) (and true (forall (?tvar_6 Int) (implies (type_of_java_dot_lang_dot_String_Array_3_4 ?tvar_6) (type_of_java_dot_lang_dot_Object_1_2 ?tvar_6)))))) (and (and (type_of_java_dot_lang_dot_String_Array_3_4 oldAr_5) true) true)) (implies (forall (?o_0 Int) (implies (type_of_java_dot_lang_dot_Object_1_2 ?o_0) (= ?o_0 null))) (= oldAr_5 null))))
)