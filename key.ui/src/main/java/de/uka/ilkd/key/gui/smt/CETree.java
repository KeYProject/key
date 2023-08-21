/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.*;
import java.util.Map.Entry;
import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.smt.model.*;
import de.uka.ilkd.key.util.Pair;

public class CETree {
    /**
     * A comparator that sort ignoRiNG cASe. Used to sort labels.
     */
    private static final Comparator<? super Pair<? super String, ? super String>> IGNORECASE_COMPARATOR =
        (Comparator<Pair<? super String, ? super String>>) (o1, o2) -> {
            String first = o1.first + "=" + o1.second;
            String second = o2.first + "=" + o2.second;
            return first.compareToIgnoreCase(second);
        };

    /**
     * The JTree to be shown.
     */
    private JTree tree;
    /**
     * The SMT model.
     */
    private final Model model;



    public CETree(Model model) {
        super();
        this.model = model;
        model.removeUnnecessaryObjects();
        model.addAliases();
        initTree();
    }

    private void initTree() {
        tree = new JTree();
        DefaultMutableTreeNode root = constructTree();
        DefaultTreeModel tm = new DefaultTreeModel(root);
        tree.setModel(tm);
        CEMouseAdapter adapter = new CEMouseAdapter();
        tree.addMouseListener(adapter);
        // this.setLayout(new BorderLayout());
        // this.add(tree, BorderLayout.CENTER);
    }

    public JTree getTreeComponent() {
        return tree;
    }


    private DefaultMutableTreeNode constructTree() {
        DefaultMutableTreeNode root = new DefaultMutableTreeNode("Model");

        DefaultMutableTreeNode constants = new DefaultMutableTreeNode("Constants");
        fillConstants(constants);
        root.add(constants);
        DefaultMutableTreeNode heaps = new DefaultMutableTreeNode("Heaps");
        fillHeaps(heaps);
        root.add(heaps);
        DefaultMutableTreeNode locssets = new DefaultMutableTreeNode("Location Sets");
        fillLocsets(locssets);
        root.add(locssets);
        DefaultMutableTreeNode sequences = new DefaultMutableTreeNode("Sequences");
        fillSequences(sequences);
        root.add(sequences);
        return root;
    }

    private void fillHeaps(DefaultMutableTreeNode heaps) {

        for (Heap h : model.getHeaps()) {
            DefaultMutableTreeNode heap = new DefaultMutableTreeNode(h.getName());
            heaps.add(heap);
            for (ObjectVal ov : h.getObjects()) {
                DefaultMutableTreeNode object = new DefaultMutableTreeNode(ov.getName());
                heap.add(object);

                addObjectProperties(ov, object);
            }
        }
    }

    /**
     * @param ov
     * @param object
     */
    private void addObjectProperties(ObjectVal ov, DefaultMutableTreeNode object) {
        String sortName = computeSortName(ov);
        // General properties
        List<Pair<String, String>> objectProperties = computeObjectProperties(ov, sortName);
        for (Pair<String, String> property : objectProperties) {
            DefaultMutableTreeNode node =
                new DefaultMutableTreeNode(property.first + "=" + property.second);
            object.add(node);
        }
        // Fields
        DefaultMutableTreeNode fields = new DefaultMutableTreeNode("Fields");
        object.add(fields);
        List<Pair<String, String>> fieldsLabels = computeFields(ov);
        for (Pair<String, String> label : fieldsLabels) {
            DefaultMutableTreeNode name =
                new DefaultMutableTreeNode(label.first + "=" + label.second);
            fields.add(name);
        }

        // Array Fields
        if (hasArrayFields(sortName)) {
            DefaultMutableTreeNode arrayFields = new DefaultMutableTreeNode("Array Fields");
            object.add(arrayFields);
            List<String> arrayFieldLabels = computeArrayFields(ov);
            for (String field : arrayFieldLabels) {
                DefaultMutableTreeNode arrayField = new DefaultMutableTreeNode(field);
                arrayFields.add(arrayField);
            }
        }


        // Fun Values
        DefaultMutableTreeNode functionValues = new DefaultMutableTreeNode("Functions");
        object.add(functionValues);
        List<Pair<String, String>> functionLabels = computeFunctions(ov);
        for (Pair<String, String> functionLabel : functionLabels) {
            DefaultMutableTreeNode fun =
                new DefaultMutableTreeNode(functionLabel.first + "=" + functionLabel.second);
            functionValues.add(fun);
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

    private void fillLocsets(DefaultMutableTreeNode locsets) {
        for (LocationSet ls : model.getLocsets()) {
            DefaultMutableTreeNode locset = new DefaultMutableTreeNode(computeLocationSetName(ls));
            locsets.add(locset);
            addLocSetProperties(ls, locset);
        }
    }

    public static String computeLocationSetName(LocationSet ls) {
        return Model.removePipes(ls.getName());
    }

    /**
     * @param ls
     * @param locset
     */
    private void addLocSetProperties(LocationSet ls, DefaultMutableTreeNode locset) {
        List<String> locationNames = computeLocationSetProperties(ls);
        for (String locationName : locationNames) {
            DefaultMutableTreeNode locationNode = new DefaultMutableTreeNode(locationName);
            locset.add(locationNode);
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

    private void fillSequences(DefaultMutableTreeNode sequences) {

        for (Sequence s : model.getSequences()) {
            DefaultMutableTreeNode sequence = new DefaultMutableTreeNode(computeSequenceName(s));
            sequences.add(sequence);
            addSequenceProperties(s, sequence);
        }


    }

    public static String computeSequenceName(Sequence s) {
        return Model.removePipes(s.getName());
    }

    /**
     * @param s
     * @param sequence
     */
    private void addSequenceProperties(Sequence s, DefaultMutableTreeNode sequence) {
        List<String> labels = computeSequenceProperties(s);
        for (String label : labels) {
            DefaultMutableTreeNode node = new DefaultMutableTreeNode(label);
            sequence.add(node);
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

    private void fillConstants(DefaultMutableTreeNode constants) {
        List<Pair<String, String>> labels = computeConstantLabels(model);

        for (Pair<String, String> label : labels) {
            DefaultMutableTreeNode name =
                new DefaultMutableTreeNode(label.first + "=" + label.second);
            constants.add(name);
        }

    }

    public static List<Pair<String, String>> computeConstantLabels(Model model) {
        Map<String, String> map = model.getConstants();
        List<Pair<String, String>> labels = new ArrayList<>();

        for (Entry<String, String> e : map.entrySet()) {
            labels.add(new Pair<>(Model.removePipes(e.getKey()), e.getValue()));
        }

        // sort the labels alphabetically
        labels.sort(IGNORECASE_COMPARATOR);

        return labels;
    }

    private class CEMouseAdapter extends MouseAdapter {



        public CEMouseAdapter() {
            super();

        }



        public void mousePressed(MouseEvent e) {
            int selRow = tree.getRowForLocation(e.getX(), e.getY());
            TreePath selPath = tree.getPathForLocation(e.getX(), e.getY());
            if (selRow != -1) {
                if (e.getClickCount() == 2) {
                    Object oNode = selPath.getLastPathComponent();
                    if (oNode instanceof DefaultMutableTreeNode) {
                        DefaultMutableTreeNode node = (DefaultMutableTreeNode) oNode;

                        if (node.getChildCount() > 0) {
                            return;
                        }

                        String value = node.getUserObject().toString();
                        if (value.contains("=")) {
                            value = value.substring(value.indexOf('=') + 1);
                        }

                        if (value.startsWith("#o")) {

                            value = value.substring(value.indexOf('=') + 1);

                            DefaultMutableTreeNode secondNode =
                                (DefaultMutableTreeNode) selPath.getPath()[1];
                            if (secondNode.getUserObject().toString().equals("Heaps")) {
                                DefaultMutableTreeNode heapNode =
                                    (DefaultMutableTreeNode) selPath.getPath()[2];
                                String heapID = heapNode.getUserObject().toString();

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

                            }


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

                        tree.expandPath(selPath);



                    }

                }
            }
        }
    }

}
