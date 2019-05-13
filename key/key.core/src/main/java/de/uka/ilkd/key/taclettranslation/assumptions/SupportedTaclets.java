// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.taclettranslation.assumptions;

import java.util.Collection;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets.TreeItem.SelectionMode;

/**
 * Change this file if you want to change the set of taclets that can be used
 * for external provers. REMARK: Adding taclets at this point does not
 * automatically mean that the added taclets are used for external provers. It
 * also depends on: 1. the taclet fulfills the condition that are checked while
 * translating.
 * 
 */
public final class SupportedTaclets {

        public static final SupportedTaclets REFERENCE = new SupportedTaclets();
        private static int IDCounter =0;
        public final int ID = IDCounter++;

        /**
         * The taclets that could be used for external provers.
         */

        private Map<String, TreeItem> tacletNames = new LinkedHashMap<String, TreeItem>();

        private SupportedTaclets() {
                getTreeModel();
           
        }

        public SupportedTaclets(String[] selected) {
                copy(REFERENCE);
            
                for(String taclet : selected){
                        TreeItem item = tacletNames.get(taclet);
                        if(item != null){
                                item.setMode(SelectionMode.all);
                        }
                }
                this.validateSelectionModes();
        }

        private void copy(SupportedTaclets reference) {

                TreeItem root = copy((TreeItem) reference.getTreeModel()
                                .getRoot());
                model = new DefaultTreeModel(root);
        }



        private TreeItem copy(TreeItem reference) {
                TreeItem newNode = reference.clone();
                tacletNames.put(newNode.text, newNode);
                Enumeration<?> en = reference.children();
                while (en.hasMoreElements()) {
                        newNode.add(copy((TreeItem)en.nextElement()));
                        
                }
                return newNode;
        }

        public void selectTaclets(String... taclets) {
                for (String taclet : taclets) {
                        TreeItem item = tacletNames.get(taclet);
                        if(item != null){
                                item.setMode(SelectionMode.all);
                        }
                }
                validateSelectionMode((TreeItem) model.getRoot());
        }

        public String[] getNamesOfSelectedTaclets() {
                List<String> list = new LinkedList<String>();
                Enumeration<?> en = ((TreeItem) model.getRoot())
                                .breadthFirstEnumeration();
                while (en.hasMoreElements()) {
                        TreeItem item = (TreeItem)en.nextElement();
                        if (item.isLeaf() && item.isSelected()) {
                                list.add(item.text);
                        }

                }
                String []result = new String[list.size()];
                return list.toArray(result);
        }



        public boolean atLeastOneTacletIsSelected() {
                return ((TreeItem) model.getRoot()).mode == SelectionMode.all
                                || ((TreeItem) model.getRoot()).mode == SelectionMode.user;
        }



        private TreeModel model = null;



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

        public int getTreeSize() {

                return getTreeModel().getChildCount(getTreeModel().getRoot()) + 1;
        }

        /**
     * 
     */
        public HashSet<String> getTacletNamesAsHash() {
                HashSet<String> names = new LinkedHashSet<String>();
                names.addAll(tacletNames.keySet());
                return names;
        }

        public Collection<String> getTacletNames() {
                return tacletNames.keySet();
        }

        /**
         * Checks whether a taclet specified by its name can be used for
         * external provers.
         * 
         * @param tacletname
         *                the name of the taclet
         * @return <code>true</code> if the taclet can be used for external
         *         provers.
         */
        public boolean contains(String tacletname, boolean mustBeSelected) {

                TreeItem item = tacletNames.get(tacletname);
            
                return item != null && (!mustBeSelected || item.isSelected());
                // return usedTaclets.contains(tacletname);
        }

        private void selectNothing() {
                for (TreeItem item : tacletNames.values()) {
                        item.setMode(TreeItem.SelectionMode.nothing);
                }

        }

        public void selectCategory(Category cat) {
                selectNothing();
                selectCategory(cat, (TreeItem) model.getRoot());
                validateSelectionModes();
        }

        private boolean selectCategory(Category cat, TreeItem node) {
                if (node.getCategory() == cat) {
                        selectAll(node);
                        return true;
                }
                for (int i = 0; i < node.getChildCount(); i++) {
                        if (selectCategory(cat, (TreeItem) node.getChildAt(i))) {
                                return true;
                        }
                }
                return false;
        }

        private void selectAll(TreeItem node) {
                node.setMode(TreeItem.SelectionMode.all);
                for (int i = 0; i < node.getChildCount(); i++) {
                        selectAll((TreeItem) node.getChildAt(i));
                }
        }

        public void validateSelectionModes() {
                validateSelectionMode((TreeItem) getTreeModel().getRoot());
        }

        private TreeItem.SelectionMode validateSelectionMode(TreeItem node) {

                if (node.isLeaf()) {
                        if (node.getMode() == TreeItem.SelectionMode.all) {
                                node.setSelectedChildCount(1);
                        } else {
                                node.setSelectedChildCount(0);
                        }

                        return node.getMode();
                }
     

                int iAll = 0, iNothing = 0;
                for (int i = 0; i < node.getChildCount(); i++) {

                        TreeNode child = node.getChildAt(i);
                        TreeItem.SelectionMode childMode = validateSelectionMode((TreeItem) child);
                        if (childMode.equals(TreeItem.SelectionMode.all)) {
                                iAll++;
                        } else if (childMode
                                        .equals(TreeItem.SelectionMode.nothing)) {
                                iNothing++;
                        }
                        TreeItem childItem = (TreeItem) child;
           

                        node.setSelectedChildCount(node.getSelectedChildCount()
                                        + childItem.getSelectedChildCount());

                }

                if (iAll == node.getChildCount()) {
                        node.setMode(TreeItem.SelectionMode.all);

                } else if (iNothing == node.getChildCount()) {
                        node.setMode(TreeItem.SelectionMode.nothing);
                } else {
                        node.setMode(TreeItem.SelectionMode.user);
                }

                return node.getMode();

        }

        private void addTaclet(TreeItem node, String taclet,
                        int genericCount) {
                addTaclet(node, taclet, true, genericCount);
        }

        /**
         * Adds a taclet to the list of supported taclets.
         * 
         * @param node
         *                the TreeNode the taclet belongs to.
         * @param taclet
         *                the name of the taclet.
         */
        private void addTaclet(TreeItem node, String taclet) {
                addTaclet(node, taclet, 0);
        }

        private void addTaclet(TreeItem node, String... taclets) {
                for (String taclet : taclets) {
                        addTaclet(node, taclet);
                }
        }

        private void addTaclet(TreeItem node, String taclet,
                        boolean checked, int genericCount) {
                TreeItem child = new TreeItem(taclet, genericCount);
                if (!tacletNames.containsKey(child.toString())) {
                        tacletNames.put(child.toString(), child);
                        node.add(child);
                }
        }

        /**
         * Adds an inner node to the tree. Inner nodes do not represents taclets
         * but the category taclets belonging to.
         * 
         * @param root
         *                the parent of the node.
         * @param text
         *                the description of the node.
         * @return returns the created node.
         */
        private TreeItem newNode(TreeItem root, String text, Category cat) {
                TreeItem node = new TreeItem(text, cat);
                root.add(node);
               
      
                return node;
        }

        /** The category of taclets. */
        public enum Category {
                ALL_SUPPORTED, PROOF_DEPENDENT, PROOF_INDEPENDENT, BOOLEAN_RULES, INTEGER_RULES, CONSTANT_REPLACEMENT_RULES, TRANSLATION_JAVA_OPERATOR, CAST_OPERATOR, MISCELLANEOUS, EXACT_INSTANCE_RULES, ONLY_CREATED_OBJECTS_ARE_REFERENCED, ONLY_CREATED_OBJECTS_ARE_REFERENCED_NORMAL, ONLY_CREATED_OBJECTS_ARE_REFERENCED_ARRAY, SYTEM_INVARIANTS, NEXT_TO_CREATE, ARRAY_LENGTH, CLASS_INITIALISATION, NO_CATEGORY, LOC_SETS, LOC_SETS_AXIOMS, LOC_SETS_LEMATA, HEAP, HEAP_AXIOMS, HEAP_LEMATA, REACH, REACH_AXIOMS, REACH_LEMATA

        }

    /**
         * This is the real interesting method of this class. Change this method
         * to change the range of supported taclets.
         * 
         * @return returns the tree model that contains all supported taclets.
         */
        public TreeModel getTreeModel() {

                if (model != null) {
                        return model;
                }

                TreeItem root = new TreeItem("Supported taclets",
                                Category.ALL_SUPPORTED);
                
                TreeItem node2 = newNode(root, "boolean rules",
                                Category.BOOLEAN_RULES);
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

                //
                // // intRules
                TreeItem node3 = newNode(root, "integer rules",
                                Category.INTEGER_RULES);
                addTaclet(node3, "expand_inByte");
                addTaclet(node3, "expand_inChar");
                addTaclet(node3, "expand_inShort");
                addTaclet(node3, "expand_inInt");
                addTaclet(node3, "expand_inLong");

                TreeItem node4 = newNode(root, "constant replacement rules",
                                Category.CONSTANT_REPLACEMENT_RULES);
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

                TreeItem node5 = newNode(root,
                                "translation of java operators",
                                Category.TRANSLATION_JAVA_OPERATOR);
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

               TreeItem node7 = newNode(root, "cast operator",
                                Category.CAST_OPERATOR);
                addTaclet(node7, "castDel", 1);
                addTaclet(node7, "typeEq", 2);
                addTaclet(node7, "typeEqDerived", 2);
                addTaclet(node7, "typeEqDerived2", 2);
                addTaclet(node7, "typeStatic", 1);
                addTaclet(node7, "closeType", 3);
                addTaclet(node7, "closeTypeSwitched", 3);

                TreeItem node9 = newNode(root,
                                "exact instance rules",
                                Category.EXACT_INSTANCE_RULES);
                addTaclet(node9, "exact_instance_definition_int");
                addTaclet(node9, "exact_instance_definition_boolean");
                addTaclet(node9, "exact_instance_definition_null", 1);
                addTaclet(node9,
                                "exact_instance_for_interfaces_or_abstract_classes",
                                2);

                TreeItem node16 = newNode(root,
                                "class initialisation",
                                Category.CLASS_INITIALISATION);
                addTaclet(node16, "class_being_initialized_is_prepared");
                addTaclet(node16, "initialized_class_is_prepared");
                addTaclet(node16, "initialized_class_is_not_erroneous");
                addTaclet(node16,
                                "class_initialized_excludes_class_init_in_progress");
                addTaclet(node16, "class_erroneous_excludes_class_in_init");
                addTaclet(node16,
                                "erroneous_class_has_no_initialized_sub_class");
                addTaclet(node16,
                                "superclasses_of_initialized_classes_are_prepared");

                TreeItem node17 = newNode(root, "LocSets", Category.LOC_SETS);
                TreeItem node20 = newNode(node17, "Axioms",
                                Category.LOC_SETS_AXIOMS);
                addTaclet(node20, "elementOfEmpty", "elementOfAllLocs",
                                "elementOfSingleton", "elementOfUnion",
                                "elementOfIntersect", "elementOfSetMinus",
                                "elementOfAllFields", "elementOfAllObjects",
                                "elementOfArrayRange", "elementOfFreshLocs",

                                "equalityToElementOf", "subsetToElementOf",
                                "disjointToElementOf",
                                "createdInHeapToElementOf"

                );

                TreeItem node21 = newNode(node17, "Lemata",
                                Category.LOC_SETS_LEMATA);
                addTaclet(node21, "elementOfEmptyEQ", "elementOfAllLocsEQ",
                                "elementOfSingletonEQ", "elementOfUnionEQ",
                                "elementOfIntersectEQ", "elementOfSetMinusEQ",
                                "elementOfAllFieldsEQ",
                                "elementOfAllObjectsEQ",
                                "elementOfArrayRangeEQ",
                                "elementOfFreshLocsEQ", "unionWithEmpty1",
                                "unionWithEmpty2", "unionWithAllLocs1",
                                "unionWithAllLocs2", "intersectWithEmpty1",
                                "intersectWithEmpty2", "intersectWithAllLocs1",
                                "intersectWithAllLocs2", "setMinusWithEmpty1",
                                "setMinusWithEmpty2", "setMinusWithAllLocs",
                                "subsetWithEmpty", "subsetWithAllLocs",
                                "disjointWithEmpty1", "disjointWithEmpty2",
                                "createdInHeapWithEmpty",
                                "createdInHeapWithSingleton",
                                "createdInHeapWithUnion",
                                "createdInHeapWithSetMinusFreshLocs",
                                "createdInHeapWithAllFields",
                                "createdInHeapWithArrayRange",
                                "referencedObjectIsCreatedRight",
                                "referencedObjectIsCreatedRightEQ",
                                "unionWithItself", "intersectWithItself",
                                "setMinusItself", "subsetOfItself");

                TreeItem node18 = newNode(root, "Heap", Category.HEAP);

                TreeItem node22 = newNode(node18, "Axioms",
                                Category.HEAP_AXIOMS);

                addTaclet(node22, "selectOfStore", "selectOfCreate",
                                "selectOfAnon", "selectOfMemset",

                                "onlyCreatedObjectsAreReferenced",
                                "onlyCreatedObjectsAreInLocSets",
                                "onlyCreatedObjectsAreInLocSetsEQ",
                                "arrayLengthNotNegative",
                                "wellFormedStoreObject",
                                "wellFormedStoreLocSet",
                                "wellFormedStorePrimitive", "wellFormedCreate",
                                "wellFormedAnon", "wellFormedMemsetObject",
                                "wellFormedMemsetLocSet",
                                "wellFormedMemsetPrimitive");

                TreeItem node23 = newNode(node18, "Lemata",
                                Category.HEAP_LEMATA);
                addTaclet(node23, "selectOfStoreEQ", "selectOfCreateEQ",
                                "selectOfAnonEQ", "selectOfMemsetEQ",
                                "memsetEmpty", "selectCreatedOfAnonEQ",

                                "wellFormedStoreObjectEQ",
                                "wellFormedStoreLocSetEQ",
                                "wellFormedStorePrimitiveEQ",
                                "wellFormedAnonEQ", "wellFormedMemsetObjectEQ",
                                "wellFormedMemsetPrimitiveEQ");

                TreeItem node19 = newNode(root, "Reach", Category.REACH);

                TreeItem node24 = newNode(node19, "Axioms",
                                Category.REACH_AXIOMS);
                addTaclet(node24, "accDefinition", "reachDefinition");

                TreeItem node25 = newNode(node19, "Lemmas",
                                Category.REACH_LEMATA);
                addTaclet(node25, "reachZero", "reachOne", "reachNull",
                                "reachNull2", "reachAddOne", "reachAddOne2",
                                "reachUniquePathSameObject",
                                "reachDependenciesStoreSimple",
                                "reachDoesNotDependOnCreatedness",
                                "reachDependenciesStore",
                                "reachDependenciesAnon",
                                "reachDependenciesAnonCoarse",
                                "only_created_objects_are_reachable",
                                "reach_does_not_depend_on_fresh_locs",
                                "reach_does_not_depend_on_fresh_locs_EQ"

                );

                model = new DefaultTreeModel(root);
                return model;
        }

        public String toString() {
                String s = "+";
                return toString((TreeItem) getTreeModel().getRoot(), s);
        }

        private String toString(TreeItem node, String s) {
                String result;

                result = "\n" + s + node.toComplexString();
                for (int i = 0; i < node.getChildCount(); i++) {
                        result += toString((TreeItem) node.getChildAt(i), s
                                        + "+");
                }

                return result;
        }

        /**
         * @return All taclet names of taclets that should be used but that are
         *         not available. Use this method only for testing. It uses only
         *         simple data structure, so that the necessary time is in
         *         O(n^2)
         */
        public Collection<String> getMissingTaclets(Collection<Taclet> taclets) {
                LinkedList<String> list = new LinkedList<String>();

                for (String name : this.tacletNames.keySet()) {
                        boolean found = false;
                        for (Taclet taclet : taclets) {
                                if (taclet.name().toString().equals(name)) {
                                        found = true;
                                        break;
                                }
                        }
                        if (!found) {
                                list.add(name);
                        }
                }
                return list;
        }

        /**
         * TreeItem represents the user data in a tree model.
         * 
         */
        public static class TreeItem extends DefaultMutableTreeNode {
        
                private static final long serialVersionUID = 1L;

                public enum SelectionMode {
                        all, nothing, user
                }

            private String text;

                private SelectionMode mode = SelectionMode.nothing;
                private int selectedChildCount = 0;
   
                private int genericCount = 0;
                private SupportedTaclets.Category category = SupportedTaclets.Category.NO_CATEGORY;

                TreeItem(String text, int genericCount) {
                        this.text = text;
                        this.genericCount = genericCount;
                }

                TreeItem(String text, SupportedTaclets.Category cat) {
                        this.text = text;
                        this.category = cat;
                }

                TreeItem(String text, boolean checked) {
                        this.text = text;

                }

                public TreeItem clone() {
                        return new TreeItem(text, mode, selectedChildCount,
                                         genericCount, category );
                }

                private TreeItem(String text, SelectionMode mode,
                                int selectedChildCount, 
                                int genericCount, Category category) {
                        super();
                        this.text = text;
                        this.mode = mode;
                        this.selectedChildCount = selectedChildCount;
                        this.genericCount = genericCount;
                        this.category = category;
                }

                public boolean isSelected() {
                        return mode.equals(SelectionMode.all)
                                        || mode.equals(SelectionMode.user);
                }

                public SupportedTaclets.Category getCategory() {
                        return category;
                }

                public int getGenericCount() {
                        return genericCount;
                }

                public int getSelectedChildCount() {
                        return selectedChildCount;
                }

                public void setSelectedChildCount(int selectedChildCount) {
                        this.selectedChildCount = selectedChildCount;
                }

             

              

                public SelectionMode getMode() {
                        return mode;
                }

                public void setMode(SelectionMode mode) {
                        this.mode = mode;
                }

                public String toComplexString() {
                        return mode.name() + ";" + category.name() + ";" + text;
                }

                public String toString() {
                        return text;
                }

                public int hashCode() {
                        return text.hashCode();
                }

        }

}
