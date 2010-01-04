// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.HashSet;

/**
 * Change this file if you want to change the set of taclets that can be used
 * for external provers. REMARK: Adding taclets at this point does not
 * automatically mean that the added taclets are used for external provers. It
 * also depends on: 1. the taclet fulfills the condition that are checked while
 * translating.
 * 
 */
final class UsedTaclets {
    /**
     * The taclets that could be used for external provers.
     */
    static private HashSet<String> usedTaclets = null;
    
    /**
     * Use this field, to allow only special taclets that are listed 
     * in the method <code>contains</code>. Use this method only for
     * testing the taclet translation.
     * If </code>testTaclets</code> is <code>null</code> all taclets
     * listed in <code>contains</code> are used (should be the normal
     * case).
     */
    static final private String testTaclets[] = {//"identical_object_equal_index"
					//"only_created_object_are_referenced_by_arrays",
						   //"array_length_non_negative"
	    					 //"only_created_object_are_referenced",
	    					 //"created_add_known_index_in_bounds",
	    					 //"created_add_known_index_in_bounds_sym",
	    					 //"created_add_known_index_in_bounds_2"
				
							//"array_length_short_javacard"
	//"array_length_non_negative"
						//    "only_created_object_are_referenced_right",
						//    "only_created_object_are_referenced_by_arrays",
						//    "only_created_object_are_referenced_non_null2"
						  // "array_length_non_negative",
						  // "array_length_non_negative_2",
						  // "array_length_non_negative_3",
						  // "array_length_short_javacard"
	//"only_created_object_are_referenced_non_null"
						
						    // ,"boolean_equal_2"
						    // ,"disjoint_repositories"
						   //  ,"castDel"
						    //,"boolean_not_equal_1"
						     //,"exact_instance_definition_int"
						     //, "exact_instance_definition_known"
						   // ,"exact_instance_definition_known_false"
						   };

    /**
     * Checks whether a taclet specified by its name can be used for external
     * provers.
     * 
     * @param tacletname
     *            the name of the taclet
     * @return <code>true</code> if the taclet can be used for external provers.
     */
    static boolean contains(String tacletname) {
	if (usedTaclets == null) {
	    usedTaclets = new HashSet<String>();

//	    // booleaRules.key
//	    usedTaclets.add("boolean_test");
//	    usedTaclets.add("all_bool");
	
	    usedTaclets.add("boolean_equal_2");
	    usedTaclets.add("boolean_not_equal_1");
	    usedTaclets.add("boolean_not_equal_2");
	    usedTaclets.add("true_to_not_false");
	    usedTaclets.add("false_to_not_true");
	    usedTaclets.add("boolean_true_commute");
	    usedTaclets.add("boolean_false_commute");
	    usedTaclets.add("apply_eq_boolean");
	    usedTaclets.add("apply_eq_boolean_2");
	    usedTaclets.add("apply_eq_boolean_rigid");
	    usedTaclets.add("apply_eq_boolean_rigid_2");
//
//	    // intRules
	    usedTaclets.add("expand_inByte");
	    usedTaclets.add("expand_inChar");
	    usedTaclets.add("expand_inShort");
	    usedTaclets.add("expand_inInt");
	    usedTaclets.add("expand_inLong");

	    usedTaclets.add("replace_byte_MAX");
	    usedTaclets.add("replace_byte_MIN");
	    usedTaclets.add("replace_char_MAX");
	    usedTaclets.add("replace_char_MIN");
	    usedTaclets.add("replace_short_MAX");
	    usedTaclets.add("replace_short_MIN");
	    usedTaclets.add("replace_int_MAX");
	    usedTaclets.add("replace_int_MIN");
	    usedTaclets.add("replace_long_MAX");
	    usedTaclets.add("replace_long_MIN");

	    usedTaclets.add("replace_byte_RANGE");
	    usedTaclets.add("replace_byte_HALFRANGE");
	    usedTaclets.add("replace_short_RANGE");
	    usedTaclets.add("replace_short_HALFRANGE");
	    usedTaclets.add("replace_char_RANGE");
	    usedTaclets.add("replace_char_HALFRANGE");
	    usedTaclets.add("replace_int_RANGE");
	    usedTaclets.add("replace_int_HALFRANGE");
	    usedTaclets.add("replace_long_RANGE");
	    usedTaclets.add("replace_long_HALFRANGE");

	    usedTaclets.add("translateJavaUnaryMinusInt");
	    usedTaclets.add("translateJavaUnaryMinusLong");
	    usedTaclets.add("translateJavaBitwiseNegation");
	    usedTaclets.add("translateJavaAddInt");
	    usedTaclets.add("translateJavaAddLong");
	    usedTaclets.add("translateJavaSubInt");
	    usedTaclets.add("translateJavaSubLong");
	    usedTaclets.add("translateJavaMulInt");
	    usedTaclets.add("translateJavaMulLong");
	    usedTaclets.add("translateJavaMod");

	    usedTaclets.add("translateJavaDivInt");
	    usedTaclets.add("translateJavaDivLong");
	    usedTaclets.add("translateJavaCastByte");
	    usedTaclets.add("translateJavaCastShort");
	    usedTaclets.add("translateJavaCastInt");
	    usedTaclets.add("translateJavaCastLong");
	    usedTaclets.add("translateJavaCastChar");
	    usedTaclets.add("translateJavaShiftRightInt");
	    usedTaclets.add("translateJavaShiftRightLong");
	    usedTaclets.add("translateJavaShiftLeftInt");

	    usedTaclets.add("translateJavaShiftLeftLong");
	    usedTaclets.add("translateJavaUnsignedShiftRightInt");
	    usedTaclets.add("translateJavaUnsignedShiftRightLong");
	    usedTaclets.add("translateJavaBitwiseOrInt");
	    usedTaclets.add("translateJavaBitwiseOrLong");
	    usedTaclets.add("translateJavaBitwiseAndInt");
	    usedTaclets.add("translateJavaBitwiseAndLong");
	    usedTaclets.add("translateJavaBitwiseXOrInt");
	    usedTaclets.add("translateJavaBitwiseXOrLong");

	     

	    // genericRules.key
	    usedTaclets.add("castDel");

	    // instanceAllocation.key
	    /** Not translatable yet. */
	    
	    usedTaclets.add("disjoint_repositories");
	    usedTaclets.add("identical_object_equal_index");
	    usedTaclets.add("boolean_is_no_int");
	    usedTaclets.add("int_is_no_boolean");
	    //usedTaclets.add("all_integer_sorts_are_equals"); 
	    
	  //  usedTaclets.add("only_created_object_are_referenced");
	    usedTaclets.add("exact_instance_definition_reference"); 
	    usedTaclets.add("exact_instance_definition_integerDomain");
	    usedTaclets.add("exact_instance_definition_int");
	    usedTaclets.add("exact_instance_definition_jbyte");
	    usedTaclets.add("exact_instance_definition_jshort");
	    usedTaclets.add("exact_instance_definition_jint");
	    usedTaclets.add("exact_instance_definition_jlong");
	    usedTaclets.add("exact_instance_definition_jchar");
	    usedTaclets.add("exact_instance_definition_boolean");
	    usedTaclets.add("exact_instance_definition_null");
	    usedTaclets.add("exact_instance_definition_known");
	    usedTaclets.add("exact_instance_definition_known_eq");
	    usedTaclets.add("exact_instance_definition_known_false");
	   
	    usedTaclets.add("exact_instance_for_interfaces_or_abstract_classes");
	     
	    usedTaclets.add("repository_object_non_null");
	    
	    //usedTaclets.add("system_invariant_for_created_2a_sym");
	    
	    usedTaclets.add("only_created_object_are_referenced");
	    usedTaclets.add("only_created_object_are_referenced_non_null");
	    usedTaclets.add("only_created_object_are_referenced_right");
	    //usedTaclets.add("only_created_object_are_referenced_by_arrays");
	    //usedTaclets.add("only_created_object_are_referenced_by_arrays_right");
	    usedTaclets.add("only_created_object_are_referenced_non_null2");
	    usedTaclets.add("only_created_object_are_referenced_non_null3");
	    //usedTaclets.add("only_created_object_are_referenced_by_arrays_2");
	    
	    
	    
	    //usedTaclets.add("only_created_object_are_referenced_by_arrays_non_null");
	    
	    
	    usedTaclets.add("system_invariant_for_created_3");
	    usedTaclets.add("system_invariant_for_created_2a_sym");
	    usedTaclets.add("system_invariant_for_created_3_sym");
	    
	    usedTaclets.add("created_inv_index_in_bounds");
	    usedTaclets.add("created_add_known_index_in_bounds");
	    usedTaclets.add("created_add_known_index_in_bounds_sym");
	    usedTaclets.add("created_add_known_index_in_bounds_2");
	    
	    
	     
	
	    
	 //   usedTaclets.add("nextToCreate_non_negative");
	    
	    
	    
	    
	   
	    
	   
	    
	    
	    usedTaclets.add("array_length_non_negative"); 
	    usedTaclets.add("array_length_non_negative_2");
	    usedTaclets.add("array_length_non_negative_3");
	    usedTaclets.add("array_length_short_javacard");
	    
	    
	    

	     

	}


	boolean found = false;
	if(testTaclets == null || testTaclets.length==0){found = true;}
	for(int i=0; i < (testTaclets == null ? 0 : testTaclets.length); i++){
	    if(testTaclets[i].equals(tacletname)){found = true;}
	}
	if(found == false) return false;
	return usedTaclets.contains(tacletname);
    }

}
