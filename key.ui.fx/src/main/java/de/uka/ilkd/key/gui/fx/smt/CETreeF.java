/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.smt;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Location;
import de.uka.ilkd.key.smt.model.LocationSet;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.model.Sequence;

import org.key_project.util.collection.Pair;

/**
 * The counterexample model tree, FX port of {@code de.uka.ilkd.key.gui.smt.CETree} (Swing
 * CETree.java:20-404): a {@link TreeView} with the Constants, Heaps, Location Sets and Sequences
 * of the SMT model. The value objects of the model (references like {@code #o5}) are leaf nodes;
 * a double click on such a leaf expands it with the properties/fields of the referenced object,
 * location set or sequence (the Swing {@code CEMouseAdapter}).
 */
public final class CETreeF {

    /**
     * A comparator that sorts ignoring case. Used to sort labels (Swing
     * {@code CETree.IGNORECASE_COMPARATOR}).
     */
    private static final Comparator<Pair<String, String>> IGNORECASE_COMPARATOR =
        (o1, o2) -> (o1.first + "=" + o1.second).compareToIgnoreCase(o2.first + "=" + o2.second);
    /** the SMT model. */
    private final Model model;

    /** the FX tree. */
    private final TreeView<String> tree;

    public CETreeF(Model model) {
        this.model = model;
        model.removeUnnecessaryObjects();
        model.addAliases();
        tree = new TreeView<>(constructTree());
        tree.setShowRoot(true);
        tree.setOnMouseClicked(this::mouseClicked);
    }

    /** @return the tree component (the Swing {@code CETree.getTreeComponent}) */
    public TreeView<String> getTreeComponent() {
        return tree;
    }

    private TreeItem<String> constructTree() {
        TreeItem<String> root = new TreeItem<>("Model");

        TreeItem<String> constants = new TreeItem<>("Constants");
        fillConstants(constants);
        root.getChildren().add(constants);
        TreeItem<String> heaps = new TreeItem<>("Heaps");
        fillHeaps(heaps);
        root.getChildren().add(heaps);
        TreeItem<String> locssets = new TreeItem<>("Location Sets");
        fillLocsets(locssets);
        root.getChildren().add(locssets);
        TreeItem<String> sequences = new TreeItem<>("Sequences");
        fillSequences(sequences);
        root.getChildren().add(sequences);
        return root;
    }

    private void fillHeaps(TreeItem<String> heaps) {
        for (Heap h : model.getHeaps()) {
            TreeItem<String> heap = new TreeItem<>(h.getName());
            heaps.getChildren().add(heap);
            for (ObjectVal ov : h.getObjects()) {
                TreeItem<String> object = new TreeItem<>(ov.getName());
                heap.getChildren().add(object);
                addObjectProperties(ov, object);
            }
        }
    }

    private void addObjectProperties(ObjectVal ov, TreeItem<String> object) {
        String sortName = computeSortName(ov);
        // General properties
        List<Pair<String, String>> objectProperties = computeObjectProperties(ov, sortName);
        for (Pair<String, String> property : objectProperties) {
            object.getChildren().add(new TreeItem<>(property.first + "=" + property.second));
        }
        // Fields
        TreeItem<String> fields = new TreeItem<>("Fields");
        object.getChildren().add(fields);
        List<Pair<String, String>> fieldsLabels = computeFields(ov);
        for (Pair<String, String> label : fieldsLabels) {
            fields.getChildren().add(new TreeItem<>(label.first + "=" + label.second));
        }

        // Array Fields
        if (hasArrayFields(sortName)) {
            TreeItem<String> arrayFields = new TreeItem<>("Array Fields");
            object.getChildren().add(arrayFields);
            List<String> arrayFieldLabels = computeArrayFields(ov);
            for (String field : arrayFieldLabels) {
                arrayFields.getChildren().add(new TreeItem<>(field));
            }
        }

        // Fun Values
        TreeItem<String> functionValues = new TreeItem<>("Functions");
        object.getChildren().add(functionValues);
        List<Pair<String, String>> functionLabels = computeFunctions(ov);
        for (Pair<String, String> functionLabel : functionLabels) {
            functionValues.getChildren()
                    .add(new TreeItem<>(functionLabel.first + "=" + functionLabel.second));
        }
    }

    public static List<Pair<String, String>> computeFunctions(ObjectVal ov) {
        List<Pair<String, String>> result = new LinkedList<>();
        for (Entry<String, String> e : ov.getFunValues().entrySet()) {
            result.add(new Pair<>(Model.removePipes(e.getKey()), e.getValue()));
        }
        return result;
    }

    public static List<String> computeArrayFields(ObjectVal ov) {
        List<String> result = new LinkedList<>();
        for (int i = 0; i < ov.getLength(); ++i) {
            result.add("[" + i + "]=" + ov.getArrayValue(i));
        }
        return result;
    }

    public static boolean hasArrayFields(String sortName) {
        return sortName.endsWith("[]");
    }

    public static String computeSortName(ObjectVal ov) {
        return ov.getSort() == null ? "java.lang.Object" : ov.getSort().name().toString();
    }

    public static List<Pair<String, String>> computeObjectProperties(ObjectVal ov,
            String sortName) {
        List<Pair<String, String>> result = new LinkedList<>();
        // Type
        sortName = Model.removePipes(sortName);
        result.add(new Pair<>("Type", sortName));

        // Exact Instance
        boolean ei = ov.isExactInstance();
        result.add(new Pair<>("Exact Instance", String.valueOf(ei)));

        // Length
        int l = ov.getLength();
        result.add(new Pair<>("Length", String.valueOf(l)));
        return result;
    }

    public static List<Pair<String, String>> computeFields(ObjectVal ov) {
        List<Pair<String, String>> labels = new ArrayList<>();

        for (Entry<String, String> e : ov.getFieldvalues().entrySet()) {
            labels.add(new Pair<>(Model.removePipes(e.getKey()), e.getValue()));
        }

        // sort the labels alphabetically
        labels.sort(IGNORECASE_COMPARATOR);
        return labels;
    }

    private void fillLocsets(TreeItem<String> locsets) {
        for (LocationSet ls : model.getLocsets()) {
            TreeItem<String> locset = new TreeItem<>(computeLocationSetName(ls));
            locsets.getChildren().add(locset);
            addLocSetProperties(ls, locset);
        }
    }

    public static String computeLocationSetName(LocationSet ls) {
        return Model.removePipes(ls.getName());
    }

    private void addLocSetProperties(LocationSet ls, TreeItem<String> locset) {
        List<String> locationNames = computeLocationSetProperties(ls);
        for (String locationName : locationNames) {
            locset.getChildren().add(new TreeItem<>(locationName));
        }
    }

    public static List<String> computeLocationSetProperties(LocationSet ls) {
        List<String> result = new LinkedList<>();
        for (int i = 0; i < ls.size(); ++i) {
            Location l = ls.get(i);
            String locationName = "(" + Model.removePipes(l.getObjectID()) + ", "
                + Model.removePipes(l.getFieldID()) + ")";
            result.add(locationName);
        }
        return result;
    }

    private void fillSequences(TreeItem<String> sequences) {
        for (Sequence s : model.getSequences()) {
            TreeItem<String> sequence = new TreeItem<>(computeSequenceName(s));
            sequences.getChildren().add(sequence);
            addSequenceProperties(s, sequence);
        }
    }

    public static String computeSequenceName(Sequence s) {
        return Model.removePipes(s.getName());
    }

    private void addSequenceProperties(Sequence s, TreeItem<String> sequence) {
        List<String> labels = computeSequenceProperties(s);
        for (String label : labels) {
            sequence.getChildren().add(new TreeItem<>(label));
        }
    }

    public static List<String> computeSequenceProperties(Sequence s) {
        List<String> result = new LinkedList<>();
        result.add("Length=" + s.getLength());

        for (int i = 0; i < s.getLength(); ++i) {
            result.add("[" + i + "]=" + Model.removePipes(s.get(i)));
        }
        return result;
    }

    private void fillConstants(TreeItem<String> constants) {
        List<Pair<String, String>> labels = computeConstantLabels(model);

        for (Pair<String, String> label : labels) {
            constants.getChildren().add(new TreeItem<>(label.first + "=" + label.second));
        }
    }

    public static List<Pair<String, String>> computeConstantLabels(Model model) {
        List<Pair<String, String>> labels = new ArrayList<>();
        for (Entry<String, String> e : model.getConstants().entrySet()) {
            labels.add(new Pair<>(Model.removePipes(e.getKey()), e.getValue()));
        }

        // sort the labels alphabetically
        labels.sort(IGNORECASE_COMPARATOR);
        return labels;
    }

    /**
     * The double-click expansion of the reference leaves (the Swing {@code CEMouseAdapter},
     * CETree.java:294-402): a leaf whose value references a model object ({@code #o}), location
     * set ({@code #l}) or sequence ({@code #s}) is expanded with the referenced entries.
     */
    private void mouseClicked(javafx.scene.input.MouseEvent e) {
        if (e.getClickCount() != 2) {
            return;
        }
        TreeItem<String> node = tree.getSelectionModel().getSelectedItem();
        if (node == null || !node.getChildren().isEmpty()) {
            return;
        }
        String value = node.getValue();
        if (value.contains("=")) {
            value = value.substring(value.indexOf('=') + 1);
        }

        if (value.startsWith("#o")) {
            value = value.substring(value.indexOf('=') + 1);

            // the referenced object sits in a heap: Model > Heaps > <heap> > <object>
            TreeItem<String> heapsAncestor = ancestorAtDepth(node, 1);
            if (heapsAncestor == null || !"Heaps".equals(heapsAncestor.getValue())) {
                return;
            }
            TreeItem<String> heapNode = ancestorAtDepth(node, 2);
            if (heapNode == null) {
                return;
            }
            String heapID = heapNode.getValue();

            // search for heap
            Heap heap = null;
            for (Heap h : model.getHeaps()) {
                if (heapID.equals(h.getName())) {
                    heap = h;
                    break;
                }
            }
            if (heap == null) {
                return;
            }

            // search for object
            ObjectVal val = null;
            for (ObjectVal o : heap.getObjects()) {
                if (o.getName().equals(value)) {
                    val = o;
                    break;
                }
            }
            if (val == null) {
                return;
            }
            addObjectProperties(val, node);
        } else if (value.startsWith("#l")) {
            LocationSet locset = null;
            for (LocationSet ls : model.getLocsets()) {
                if (ls.getName().startsWith(value)) {
                    locset = ls;
                    break;
                }
            }
            if (locset == null) {
                return;
            }
            addLocSetProperties(locset, node);
        } else if (value.startsWith("#s")) {
            Sequence sequence = null;
            for (Sequence s : model.getSequences()) {
                if (s.getName().startsWith(value)) {
                    sequence = s;
                    break;
                }
            }
            if (sequence == null) {
                return;
            }
            addSequenceProperties(sequence, node);
        }
    }

    /**
     * @param node a tree item
     * @param depth the depth of the wanted ancestor (0 = the root)
     * @return the ancestor of the given depth, or {@code null} if the node is not that deep
     */
    private static TreeItem<String> ancestorAtDepth(TreeItem<String> node, int depth) {
        TreeItem<String> current = node;
        for (int i = 0; i < depth; i++) {
            current = current.getParent();
            if (current == null) {
                return null;
            }
        }
        return current;
    }
}
