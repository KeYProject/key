// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;

/**
 * Change this file if you want to change the set of taclets that can be used
 * for external provers. REMARK: Adding taclets at this point does not
 * automatically mean that the added taclets are used for external provers. It
 * also depends on: 1. the taclet fulfills the condition that are checked while
 * translating.
 * 
 */
public final class UsedTaclets {
    
    
    public static final UsedTaclets INSTANCE = new UsedTaclets();
    
    /**
     * The taclets that could be used for external provers.
     */

    private HashMap<String, TreeItem> tacletNames = new HashMap<String, TreeItem>();
    
    private UsedTaclets(){
	getTreeModel();
    }

    private TreeModel model = null;

    /**
     * Use this field, to allow only special taclets that are listed in the
     * method <code>contains</code>. Use this method only for testing the taclet
     * translation. If </code>testTaclets</code> is <code>null</code> all
     * taclets listed in <code>contains</code> are used (should be the normal
     * case).
     */
    final private String testTaclets[] = {// "identical_object_equal_index"

    };

    /**
     * 
     * @return returns the number of taclets that are supported.
     */
    public int getCount() {
	return tacletNames.size();
    }

    /**
     * @return returns all taclets that are supported wrapped by
     *         {@link TreeItem}
     */
    public Collection<TreeItem> getTreeItems() {
	return tacletNames.values();
    }
    
    /**
     * 
     */
    public HashSet<String> getTacletNamesAsHash(){
	HashSet<String> names = new HashSet<String>();
	names.addAll(tacletNames.keySet());
	return names;
    }
    
    public Collection<String> getTacletNames(){
	return tacletNames.keySet();
    }
    

    /**
     * Checks whether a taclet specified by its name can be used for external
     * provers.
     * 
     * @param tacletname
     *            the name of the taclet
     * @return <code>true</code> if the taclet can be used for external provers.
     */
    boolean contains(String tacletname) {


	boolean found = false;
	if (testTaclets == null || testTaclets.length == 0) {
	    found = true;
	}
	for (int i = 0; i < (testTaclets == null ? 0 : testTaclets.length); i++) {
	    if (testTaclets[i].equals(tacletname)) {
		found = true;
	    }
	}
	if (found == false)
	    return false;
	TreeItem item = tacletNames.get(tacletname);
	return item != null && item.getMode() == SelectionMode.all;
	// return usedTaclets.contains(tacletname);

    }

    private TreeItem treeItem(TreeNode node) {
	return (TreeItem) ((DefaultMutableTreeNode) node).getUserObject();
    }
    
    private void selectNothing(){
	for(TreeItem item : tacletNames.values()){
	    item.setMode(SelectionMode.nothing);
	}
	
    }
    
    public void selectCategory(Category cat){
	selectNothing();
	selectCategory(cat,(TreeNode)model.getRoot());
	validateSelectionModes();
    }
    
    private boolean selectCategory(Category cat, TreeNode node){
	if(treeItem(node).getCategory() == cat){
	    selectAll(node);
	    return true;
	}
	for(int i=0; i < node.getChildCount(); i++){
	    if(selectCategory(cat, node.getChildAt(i))){
		return true;
	    }
	}
	return false;
    }
    
    private void selectAll(TreeNode node){
	treeItem(node).setMode(SelectionMode.all);
	for(int i=0; i < node.getChildCount(); i ++){
	    selectAll(node.getChildAt(i));
	}
    }

    public void validateSelectionModes(){
	TreeModel model = getTreeModel();
	validateSelectionMode((TreeNode)model.getRoot());
    }
    
    

    
    private SelectionMode validateSelectionMode(TreeNode node){
	TreeItem item = treeItem(node);
	if(node.isLeaf()){
	    if(item.getMode() == SelectionMode.all){
		item.setSelectedChildCount(1);
	    }else{
		item.setSelectedChildCount(0);
	    }
	    
	    return item.getMode();
	}
	item.setChildCount(0);
	

	int iAll=0, iNothing=0;
	for(int i=0; i < node.getChildCount(); i++){
	    
	    TreeNode child = node.getChildAt(i);
	    SelectionMode childMode = validateSelectionMode(child);
	    if(childMode.equals(SelectionMode.all)){
		iAll++;
	    }else if(childMode.equals(SelectionMode.nothing)){
		iNothing++;
	    }
	    TreeItem childItem = treeItem(child);
	    item.setChildCount(item.getChildCount()+childItem.getChildCount());
	    
	    item.setSelectedChildCount(item.getSelectedChildCount()+childItem.getSelectedChildCount());
	    
	}
	
	if(iAll == node.getChildCount()){
	    item.setMode(SelectionMode.all);
	    
	}else if(iNothing == node.getChildCount()){
	    item.setMode(SelectionMode.nothing);
	}else {
	    item.setMode(SelectionMode.user);
	}
	
	return item.getMode();

    }
    
    
    private void addTaclet(DefaultMutableTreeNode node, String taclet, int genericCount){
	addTaclet(node,taclet,true,genericCount);
    }

    /**
     * Adds a taclet to the list of supported taclets.
     * 
     * @param node
     *            the TreeNode the taclet belongs to.
     * @param taclet
     *            the name of the taclet.
     */
    private void addTaclet(DefaultMutableTreeNode node, String taclet) {
	addTaclet(node, taclet, 0);
    }

    private  void addTaclet(DefaultMutableTreeNode node, String taclet,
	    boolean checked, int genericCount) {
	TreeItem child = new TreeItem(taclet, genericCount);
	if (!tacletNames.containsKey(child.toString())) {
	    tacletNames.put(child.toString(), child);
	    node.add(new DefaultMutableTreeNode(child));
	}
    }

    /**
     * Adds an inner node to the tree. Inner nodes do not represents taclets but
     * the category taclets belonging to.
     * 
     * @param root
     *            the parent of the node.
     * @param text
     *            the description of the node.
     * @return returns the created node.
     */
    private  DefaultMutableTreeNode newNode(DefaultMutableTreeNode root,
	    String text, Category cat) {
	DefaultMutableTreeNode node = new DefaultMutableTreeNode(new TreeItem(
	        text,cat));
	root.add(node);
	return node;
    }
    
    /** The category of taclets.*/
    public enum Category  { ALL_SUPPORTED,
	                     PROOF_DEPENDENT,
	                     PROOF_INDEPENDENT,
	                     BOOLEAN_RULES,
	                     INTEGER_RULES,
	                     CONSTANT_REPLACEMENT_RULES,
	                     TRANSLATION_JAVA_OPERATOR,
	                     CAST_OPERATOR,
	                     MISCELLANEOUS,
	                     EXACT_INSTANCE_RULES,
	                     ONLY_CREATED_OBJECTS_ARE_REFERENCED,
	                     ONLY_CREATED_OBJECTS_ARE_REFERENCED_NORMAL,
	                     ONLY_CREATED_OBJECTS_ARE_REFERENCED_ARRAY,
	                     SYTEM_INVARIANTS,
	                     NEXT_TO_CREATE,
	                     ARRAY_LENGTH,
	                     CLASS_INITIALISATION,
	                     NO_CATEGORY
	            
	                     
	                };

    /**
     * This is the real interesting method of this class. Change this method to
     * change the range of supported taclets.
     * 
     * @return returns the tree model that contains all supported taclets.
     */
    public TreeModel getTreeModel() {

	if (model != null){
	    return model;
	}
	    

	TreeItem rootItem = new TreeItem("Supported taclets",Category.ALL_SUPPORTED);
	
	DefaultMutableTreeNode root = new DefaultMutableTreeNode(rootItem);

	DefaultMutableTreeNode node1 = newNode(root, "proof independent",Category.PROOF_INDEPENDENT);

	DefaultMutableTreeNode node2 = newNode(node1, "boolean rules",Category.BOOLEAN_RULES);
	addTaclet(node2, "boolean_equal_2");
	addTaclet(node2, "boolean_not_equal_1");
	addTaclet(node2, "boolean_not_equal_2");
	addTaclet(node2, "true_to_not_false");
	addTaclet(node2, "false_to_not_true");
	addTaclet(node2, "boolean_true_commute");
	addTaclet(node2, "boolean_false_commute");
	addTaclet(node2, "apply_eq_boolean");
	addTaclet(node2, "apply_eq_boolean_2");
	addTaclet(node2, "apply_eq_boolean_rigid");
	addTaclet(node2, "apply_eq_boolean_rigid_2");
	addTaclet(node2, "boolean_is_no_int");
	addTaclet(node2, "int_is_no_boolean");
	//
	// // intRules
	DefaultMutableTreeNode node3 = newNode(node1, "integer rules",Category.INTEGER_RULES);
	addTaclet(node3, "expand_inByte");
	addTaclet(node3, "expand_inChar");
	addTaclet(node3, "expand_inShort");
	addTaclet(node3, "expand_inInt");
	addTaclet(node3, "expand_inLong");

	DefaultMutableTreeNode node4 = newNode(node1,
	        "constant replacement rules",Category.CONSTANT_REPLACEMENT_RULES);
	addTaclet(node4, "replace_byte_MAX");
	addTaclet(node4, "replace_byte_MIN");
	addTaclet(node4, "replace_char_MAX");
	addTaclet(node4, "replace_char_MIN");
	addTaclet(node4, "replace_short_MAX");
	addTaclet(node4, "replace_short_MIN");
	addTaclet(node4, "replace_int_MAX");
	addTaclet(node4, "replace_int_MIN");
	addTaclet(node4, "replace_long_MAX");
	addTaclet(node4, "replace_long_MIN");

	addTaclet(node4, "replace_byte_RANGE");
	addTaclet(node4, "replace_byte_HALFRANGE");
	addTaclet(node4, "replace_short_RANGE");
	addTaclet(node4, "replace_short_HALFRANGE");
	addTaclet(node4, "replace_char_RANGE");
	addTaclet(node4, "replace_int_RANGE");
	addTaclet(node4, "replace_int_HALFRANGE");
	addTaclet(node4, "replace_long_RANGE");
	addTaclet(node4, "replace_long_HALFRANGE");

	DefaultMutableTreeNode node5 = newNode(node1,
	        "translation of java operators",Category.TRANSLATION_JAVA_OPERATOR);
	addTaclet(node5, "translateJavaUnaryMinusInt");
	addTaclet(node5, "translateJavaUnaryMinusLong");
	addTaclet(node5, "translateJavaBitwiseNegation");
	addTaclet(node5, "translateJavaAddInt");
	addTaclet(node5, "translateJavaAddLong");
	addTaclet(node5, "translateJavaSubInt");
	addTaclet(node5, "translateJavaSubLong");
	addTaclet(node5, "translateJavaMulInt");
	addTaclet(node5, "translateJavaMulLong");
	addTaclet(node5, "translateJavaMod");

	addTaclet(node5, "translateJavaDivInt");
	addTaclet(node5, "translateJavaDivLong");
	addTaclet(node5, "translateJavaCastByte");
	addTaclet(node5, "translateJavaCastShort");
	addTaclet(node5, "translateJavaCastInt");
	addTaclet(node5, "translateJavaCastLong");
	addTaclet(node5, "translateJavaCastChar");
	addTaclet(node5, "translateJavaShiftRightInt");
	addTaclet(node5, "translateJavaShiftRightLong");
	addTaclet(node5, "translateJavaShiftLeftInt");

	addTaclet(node5, "translateJavaShiftLeftLong");
	addTaclet(node5, "translateJavaUnsignedShiftRightInt");
	addTaclet(node5, "translateJavaUnsignedShiftRightLong");
	addTaclet(node5, "translateJavaBitwiseOrInt");
	addTaclet(node5, "translateJavaBitwiseOrLong");
	addTaclet(node5, "translateJavaBitwiseAndInt");
	addTaclet(node5, "translateJavaBitwiseAndLong");
	addTaclet(node5, "translateJavaBitwiseXOrInt");
	addTaclet(node5, "translateJavaBitwiseXOrLong");

	DefaultMutableTreeNode node6 = newNode(root, "proof dependent",Category.PROOF_DEPENDENT);

	DefaultMutableTreeNode node7 = newNode(node6, "cast operator",Category.CAST_OPERATOR);
	addTaclet(node7, "castDel",1);
	addTaclet(node7, "typeEq",2);
	addTaclet(node7, "typeEqDerived",2);
	addTaclet(node7, "typeEqDerived2",2);
	addTaclet(node7, "typeStatic",1);
	addTaclet(node7, "castType",4);
	addTaclet(node7, "castType2",4);
	addTaclet(node7, "closeType",3);
	addTaclet(node7, "closeTypeSwitched",3);

	DefaultMutableTreeNode node8 = newNode(node6, "miscellaneous",Category.MISCELLANEOUS);
	addTaclet(node8, "disjoint_repositories",2);
	addTaclet(node8, "identical_object_equal_index",1);

	addTaclet(node8, "repository_object_non_null",1);

	DefaultMutableTreeNode node9 = newNode(node6, "exact instance rules",Category.EXACT_INSTANCE_RULES);
	addTaclet(node9, "exact_instance_definition_reference",2);
	addTaclet(node9, "exact_instance_definition_integerDomain");
	addTaclet(node9, "exact_instance_definition_int");
	addTaclet(node9, "exact_instance_definition_jbyte");
	addTaclet(node9, "exact_instance_definition_jshort");
	addTaclet(node9, "exact_instance_definition_jint");
	addTaclet(node9, "exact_instance_definition_jlong");
	addTaclet(node9, "exact_instance_definition_jchar");
	addTaclet(node9, "exact_instance_definition_boolean");
	addTaclet(node9, "exact_instance_definition_null",1);
	addTaclet(node9, "exact_instance_definition_known",1);
	addTaclet(node9, "exact_instance_definition_known_eq",2);
	addTaclet(node9, "exact_instance_definition_known_false",2);
	addTaclet(node9, "exact_instance_for_interfaces_or_abstract_classes",2);
	addTaclet(node9, "exact_instance_definition_known_eq_false",3); // n^3!!!

	// usedTaclets.add("system_invariant_for_created_2a_sym");
	DefaultMutableTreeNode node10 = newNode(node6,
	        "only created objects are referenced...",Category.ONLY_CREATED_OBJECTS_ARE_REFERENCED);

	DefaultMutableTreeNode node11 = newNode(node10, "normal",Category.ONLY_CREATED_OBJECTS_ARE_REFERENCED_NORMAL);
	addTaclet(node11, "only_created_object_are_referenced",1);
	addTaclet(node11, "only_created_object_are_referenced_non_null",1);
	addTaclet(node11, "only_created_object_are_referenced_right",1);
	addTaclet(node11, "only_created_object_are_referenced_non_null2",2);
	addTaclet(node11, "only_created_object_are_referenced_non_null3",2);
	
	// Arrays are not supported yet: SMT-Translation does not work.
	// Taclet translation works!
//	DefaultMutableTreeNode node12 = newNode(node10, "array");
//	addTaclet(node12, "only_created_object_are_referenced_by_arrays");
//	addTaclet(node12, "only_created_object_are_referenced_by_arrays_right");
//	addTaclet(node12, "only_created_object_are_referenced_by_arrays_2");
//	addTaclet(node12,
//	        "only_created_object_are_referenced_by_arrays_non_null");

	DefaultMutableTreeNode node13 = newNode(node6, "system invariants",Category.SYTEM_INVARIANTS);

	addTaclet(node13, "system_invariant_for_created_3",2);
	addTaclet(node13, "system_invariant_for_created_2a_sym",2);
	addTaclet(node13, "system_invariant_for_created_3_sym",2);

	DefaultMutableTreeNode node14 = newNode(node6, "nextToCreate",Category.NEXT_TO_CREATE);
	addTaclet(node14, "created_inv_index_in_bounds",2);
	addTaclet(node14, "created_add_known_index_in_bounds",2);
	addTaclet(node14, "created_add_known_index_in_bounds_sym",2);
	addTaclet(node14, "created_add_known_index_in_bounds_2",2);
	addTaclet(node14,
	        "objects_with_index_geq_next_to_create_are_not_created",2);
	addTaclet(
	        node14,
	        "objects_with_index_greater_next_to_create_are_not_createdsystem" +
	        "_invariant_for_created_2a_automated_use_3",2);
	addTaclet(node8, "nextToCreate_non_negative");
	addTaclet(node8, "nextToCreate_non_negative_2");

	DefaultMutableTreeNode node15 = newNode(node6, "array length",Category.ARRAY_LENGTH);
	addTaclet(node15, "array_length_non_negative",1);
	addTaclet(node15, "array_length_non_negative_2",1);
	addTaclet(node15, "array_length_non_negative_3",1);
	addTaclet(node15, "array_length_short_javacard",1);

	DefaultMutableTreeNode node16 = newNode(node6, "class initialisation",Category.CLASS_INITIALISATION);
	addTaclet(node16, "class_being_initialized_is_prepared");
	addTaclet(node16, "initialized_class_is_prepared");
	addTaclet(node16, "initialized_class_is_not_erroneous");
	addTaclet(node16, "class_initialized_excludes_class_init_in_progress");
	addTaclet(node16, "class_erroneous_excludes_class_in_init");
	addTaclet(node16, "erroneous_class_has_no_initialized_sub_class");
	addTaclet(node16, "superclasses_of_initialized_classes_are_initialized");
	addTaclet(node16,
	        "superclasses_of_initialized_classes_are_initialized_2");

	model = new DefaultTreeModel(root);
	return model;
    }
    
    public String toString(){
	String s = "+";
	return toString((TreeNode)getTreeModel().getRoot(),s);
    }
    
    private String toString(TreeNode node,String s){
	String result;
	
	result = "\n"+s+treeItem(node).toComplexString();
	for(int i=0; i < node.getChildCount(); i ++){
	    result+= toString(node.getChildAt(i),s+"+");
	}
	
	return result;
    }

}
