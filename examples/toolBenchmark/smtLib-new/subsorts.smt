( benchmark KeY-translation

 :logic AUFLIA
 :extrasorts ()
:extrapreds ((type_of_java_dot_lang_dot_String_Array_3_4 Int ) (type_of_java_dot_lang_dot_Object_1_2 Int ) )
:extrafuns ((dummy_java_dot_lang.Object_7 Int ) (oldAr_5 Int ) (dummy_java_dot_lang.String_Array_6 Int ) (null Int ) )
:assumption (type_of_java_dot_lang_dot_Object_1_2 dummy_java_dot_lang.Object_7)
:assumption (type_of_java_dot_lang_dot_String_Array_3_4 oldAr_5)
:assumption (type_of_java_dot_lang_dot_String_Array_3_4 dummy_java_dot_lang.String_Array_6)
:assumption (forall (?tvar_8 Int) (implies (type_of_java_dot_lang_dot_String_Array_3_4 ?tvar_8) (type_of_java_dot_lang_dot_Object_1_2 ?tvar_8)))
:assumption (type_of_java_dot_lang_dot_String_Array_3_4 null)
:assumption (type_of_java_dot_lang_dot_Object_1_2 null)
:formula (not (implies true (implies (forall (?o_0 Int) (implies (type_of_java_dot_lang_dot_Object_1_2 ?o_0) (= ?o_0 null))) (= oldAr_5 null))))
)