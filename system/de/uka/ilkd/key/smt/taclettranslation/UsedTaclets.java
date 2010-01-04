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

import java.util.HashMap;
import java.util.HashSet;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;

/**
 * Change this file if you want to change the set of taclets that can be used
 * for external provers. REMARK: Adding taclets at this point does not
 * automatically mean that the added taclets are used for external provers. It
 * also depends on: 1. the taclet fulfills the condition that are checked while
 * translating.
 * 
 */
public final class UsedTaclets {
    /**
     * The taclets that could be used for external provers.
     */
    static private HashSet<String> usedTaclets = null;
    static private HashMap<String,TreeItem> taclets = new HashMap<String,TreeItem>();
   private static TreeModel model = null;
    
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
	getTreeModel();

	boolean found = false;
	if(testTaclets == null || testTaclets.length==0){found = true;}
	for(int i=0; i < (testTaclets == null ? 0 : testTaclets.length); i++){
	    if(testTaclets[i].equals(tacletname)){found = true;}
	}
	if(found == false) return false;
	TreeItem item = taclets.get(tacletname);
	//return item != null && item.isParentSelected() && item.isChecked();
	return usedTaclets.contains(tacletname);
	
	
    }
    
    static void addTaclet(DefaultMutableTreeNode node, String taclet){
	addTaclet(node,taclet, true);
    }
    
    static void addTaclet(DefaultMutableTreeNode node, String taclet, boolean checked){
	TreeItem child = new TreeItem(taclet,checked);
	if(!taclets.containsKey(child.toString())){
	    taclets.put(child.toString(),child);
	    node.add(new DefaultMutableTreeNode(child));
	}
    }
    
    static DefaultMutableTreeNode newNode(DefaultMutableTreeNode root, String text){
	DefaultMutableTreeNode node = new DefaultMutableTreeNode(new TreeItem(text));
	root.add(node);
	return node;
    }
    
    
    public static TreeModel getTreeModel(){
	
	if(model != null) return model;
	
	DefaultMutableTreeNode root =  new DefaultMutableTreeNode(new TreeItem("All supported taclets"));
	
	DefaultMutableTreeNode node1 = newNode(root, "proof independent");
	
	DefaultMutableTreeNode node2 = newNode(node1, "boolean rules");
	    addTaclet(node2,"boolean_equal_2");
	    addTaclet(node2,"boolean_not_equal_1");
	    addTaclet(node2,"boolean_not_equal_2");
	    addTaclet(node2,"true_to_not_false");
	    addTaclet(node2,"false_to_not_true");
	    addTaclet(node2,"boolean_true_commute");
	    addTaclet(node2,"boolean_false_commute");
	    addTaclet(node2,"apply_eq_boolean");
	    addTaclet(node2,"apply_eq_boolean_2");
	    addTaclet(node2,"apply_eq_boolean_rigid");
	    addTaclet(node2,"apply_eq_boolean_rigid_2");
//
//	    // intRules
	DefaultMutableTreeNode node3 = newNode(node1, "integer rules");
	    addTaclet(node3,"expand_inByte");
	    addTaclet(node3,"expand_inChar");
	    addTaclet(node3,"expand_inShort");
	    addTaclet(node3,"expand_inInt");
	    addTaclet(node3,"expand_inLong");

	DefaultMutableTreeNode node4 = newNode(node1, "constant replacement rules");
	    addTaclet(node4,"replace_byte_MAX");
	    addTaclet(node4,"replace_byte_MIN");
	    addTaclet(node4,"replace_char_MAX");
	    addTaclet(node4,"replace_char_MIN");
	    addTaclet(node4,"replace_short_MAX");
	    addTaclet(node4,"replace_short_MIN");
	    addTaclet(node4,"replace_int_MAX");
	    addTaclet(node4,"replace_int_MIN");
	    addTaclet(node4,"replace_long_MAX");
	    addTaclet(node4,"replace_long_MIN");

	    addTaclet(node4,"replace_byte_RANGE");
	    addTaclet(node4,"replace_byte_HALFRANGE");
	    addTaclet(node4,"replace_short_RANGE");
	    addTaclet(node4,"replace_short_HALFRANGE");
	    addTaclet(node4,"replace_char_RANGE");
	    addTaclet(node4,"replace_char_HALFRANGE");
	    addTaclet(node4,"replace_int_RANGE");
	    addTaclet(node4,"replace_int_HALFRANGE");
	    addTaclet(node4,"replace_long_RANGE");
	    addTaclet(node4,"replace_long_HALFRANGE");

	DefaultMutableTreeNode node5 = newNode(node1, "translating of java operators");
	    addTaclet(node5,"translateJavaUnaryMinusInt");
	    addTaclet(node5,"translateJavaUnaryMinusLong");
	    addTaclet(node5,"translateJavaBitwiseNegation");
	    addTaclet(node5,"translateJavaAddInt");
	    addTaclet(node5,"translateJavaAddLong");
	    addTaclet(node5,"translateJavaSubInt");
	    addTaclet(node5,"translateJavaSubLong");
	    addTaclet(node5,"translateJavaMulInt");
	    addTaclet(node5,"translateJavaMulLong");
	    addTaclet(node5,"translateJavaMod");

	    addTaclet(node5,"translateJavaDivInt");
	    addTaclet(node5,"translateJavaDivLong");
	    addTaclet(node5,"translateJavaCastByte");
	    addTaclet(node5,"translateJavaCastShort");
	    addTaclet(node5,"translateJavaCastInt");
	    addTaclet(node5,"translateJavaCastLong");
	    addTaclet(node5,"translateJavaCastChar");
	    addTaclet(node5,"translateJavaShiftRightInt");
	    addTaclet(node5,"translateJavaShiftRightLong");
	    addTaclet(node5,"translateJavaShiftLeftInt");

	    addTaclet(node5,"translateJavaShiftLeftLong");
	    addTaclet(node5,"translateJavaUnsignedShiftRightInt");
	    addTaclet(node5,"translateJavaUnsignedShiftRightLong");
	    addTaclet(node5,"translateJavaBitwiseOrInt");
	    addTaclet(node5,"translateJavaBitwiseOrLong");
	    addTaclet(node5,"translateJavaBitwiseAndInt");
	    addTaclet(node5,"translateJavaBitwiseAndLong");
	    addTaclet(node5,"translateJavaBitwiseXOrInt");
	    addTaclet(node5,"translateJavaBitwiseXOrLong");

	     

	DefaultMutableTreeNode node6 = newNode(root, "proof depending");
	
	DefaultMutableTreeNode node7 = newNode(node6, "cast operator");
	    addTaclet(node7,"castDel");

	    // instanceAllocation.key

	DefaultMutableTreeNode node8 = newNode(node6, "not yet described");
	    addTaclet(node8,"disjoint_repositories");
	    addTaclet(node8,"identical_object_equal_index");
	    addTaclet(node8,"boolean_is_no_int");
	    addTaclet(node8,"int_is_no_boolean");
	    addTaclet(node8,"repository_object_non_null");
	    //usedTaclets.add("all_integer_sorts_are_equals"); 
	    
	  //  usedTaclets.add("only_created_object_are_referenced");
	DefaultMutableTreeNode node9 = newNode(node6, "exact instance rules");
	    addTaclet(node9,"exact_instance_definition_reference"); 
	    addTaclet(node9,"exact_instance_definition_integerDomain");
	    addTaclet(node9,"exact_instance_definition_int");
	    addTaclet(node9,"exact_instance_definition_jbyte");
	    addTaclet(node9,"exact_instance_definition_jshort");
	    addTaclet(node9,"exact_instance_definition_jint");
	    addTaclet(node9,"exact_instance_definition_jlong");
	    addTaclet(node9,"exact_instance_definition_jchar");
	    addTaclet(node9,"exact_instance_definition_boolean");
	    addTaclet(node9,"exact_instance_definition_null");
	    addTaclet(node9,"exact_instance_definition_known");
	    addTaclet(node9,"exact_instance_definition_known_eq");
	    addTaclet(node9,"exact_instance_definition_known_false");
	    addTaclet(node9,"exact_instance_for_interfaces_or_abstract_classes");
	     
	    
	    
	    //usedTaclets.add("system_invariant_for_created_2a_sym");
	DefaultMutableTreeNode node10 = newNode(node6, "only created objects are referenced...");
	
	DefaultMutableTreeNode node11 = newNode(node10, "normal");
	    addTaclet(node11,"only_created_object_are_referenced");
	    addTaclet(node11,"only_created_object_are_referenced_non_null");
	    addTaclet(node11,"only_created_object_are_referenced_right");
	    addTaclet(node11,"only_created_object_are_referenced_non_null2");
	    addTaclet(node11,"only_created_object_are_referenced_non_null3");
	DefaultMutableTreeNode node12 = newNode(node10, "array");
	    addTaclet(node12,"only_created_object_are_referenced_by_arrays");
	    addTaclet(node12,"only_created_object_are_referenced_by_arrays_right");
	    addTaclet(node12,"only_created_object_are_referenced_by_arrays_2");
	    addTaclet(node12,"only_created_object_are_referenced_by_arrays_non_null");
	    
        DefaultMutableTreeNode node13 = newNode(node6, "system invariants");
            
            addTaclet(node13,"system_invariant_for_created_3");
            addTaclet(node13,"system_invariant_for_created_2a_sym");
            addTaclet(node13,"system_invariant_for_created_3_sym");
	    
        DefaultMutableTreeNode node14 = newNode(node6, "nextToCreate");
            addTaclet(node14,"created_inv_index_in_bounds");
            addTaclet(node14,"created_add_known_index_in_bounds");
            addTaclet(node14,"created_add_known_index_in_bounds_sym");
            addTaclet(node14,"created_add_known_index_in_bounds_2");
            
        DefaultMutableTreeNode node15 = newNode(node6, "array length");
            addTaclet(node15,"array_length_non_negative"); 
            addTaclet(node15,"array_length_non_negative_2");
            addTaclet(node15,"array_length_non_negative_3");
            addTaclet(node15,"array_length_short_javacard");
   
	
	    
	 //   usedTaclets.add("nextToCreate_non_negative");

	   
	    
	    

	    
	
	
	model = new DefaultTreeModel(root);
	return model;
    }

}






















