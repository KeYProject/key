/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofmanagement;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.util.KeYTypeUtil;

import org.key_project.util.collection.ImmutableSet;

/**
 * JavaFX port of the Swing {@code de.uka.ilkd.key.gui.ClassTree} (module {@code key.ui}): a
 * {@link TreeView} of the loaded Java types (full class names compressed at linear path
 * segments) with their contract targets as leaves. Used by the
 * {@link ProofManagementDialogF} "By Target" tab to select a {@link KeYJavaType} and an
 * {@link IObserverFunction} whose contracts are shown in the contract panel.
 * <p>
 * The tree building ({@link #createTree}, {@link #insertIntoTree},
 * {@link #compressLinearPaths}) and the target display name ({@link #getDisplayName}) are ported
 * 1:1 from the Swing original; the Swing {@code DefaultTreeModel}/{@code TreePath} mechanics are
 * replaced by {@link TreeItem} traversal.
 */
public class ClassTreeF extends TreeView<ClassTreeF.Entry> {

    /**
     * The user object of the tree nodes (Swing {@code ClassTree.Entry}): a path segment, a Java
     * type or a contract target, depending on which fields are set.
     */
    public static class Entry {
        public String string;
        public KeYJavaType kjt = null;
        public IObserverFunction target = null;
        public int numMembers = 0;
        public int numSelectedMembers = 0;

        public Entry(String string) {
            this.string = string;
        }

        @Override
        public String toString() {
            return string;
        }
    }

    private final Services services;

    /**
     * Creates the class tree for the given services.
     *
     * @param addContractTargets whether the contract targets (methods/observers) are added as
     *        leaves below each class node
     * @param skipLibraryClasses whether library classes are hidden
     * @param services the services providing the Java information and the specification
     *        repository
     */
    public ClassTreeF(boolean addContractTargets, boolean skipLibraryClasses, Services services) {
        this.services = services;
        setRoot(createTree(addContractTargets, skipLibraryClasses, services));
        // the Swing tree hides the invisible root as well
        setShowRoot(false);
    }

    // -------------------------------------------------------------------------
    // internal methods (ported from the Swing original)
    // -------------------------------------------------------------------------

    private static TreeItem<Entry> getChildByString(TreeItem<Entry> parentNode,
            String childString) {
        for (TreeItem<Entry> childNode : parentNode.getChildren()) {
            if (childString.equals(childNode.getValue().string)) {
                return childNode;
            }
        }
        return null;
    }

    private static TreeItem<Entry> getChildByTarget(TreeItem<Entry> parentNode,
            IObserverFunction target) {
        for (TreeItem<Entry> childNode : parentNode.getChildren()) {
            if (target.equals(childNode.getValue().target)) {
                return childNode;
            }
        }
        return null;
    }

    private static void insertIntoTree(TreeItem<Entry> rootNode, KeYJavaType kjt,
            boolean addContractTargets, Services services) {
        String fullClassName = kjt.getFullName();
        int length = fullClassName.length();
        int index = -1;
        TreeItem<Entry> node = rootNode;
        do {
            // get next part of the name
            int lastIndex = index;
            index = fullClassName.indexOf('.', ++index);
            if (index == -1) {
                index = length;
            }
            String namePart = fullClassName.substring(lastIndex + 1, index);

            // try to get child node; otherwise, create and insert it
            TreeItem<Entry> childNode = getChildByString(node, namePart);
            if (childNode == null) {
                childNode = new TreeItem<>(new Entry(namePart));
                node.getChildren().add(childNode);
            }

            // go down to child node
            node = childNode;
        } while (index != length);

        // save kjt in leaf
        node.getValue().kjt = kjt;

        // add all contract targets of kjt
        if (addContractTargets) {
            final ImmutableSet<IObserverFunction> targets =
                services.getSpecificationRepository().getContractTargets(kjt);

            // sort targets alphabetically
            final IObserverFunction[] targetsArr = targets.toArray(new IObserverFunction[0]);
            Arrays.sort(targetsArr, (o1, o2) -> {
                if (o1 instanceof IProgramMethod && !(o2 instanceof IProgramMethod)) {
                    return -1;
                } else if (!(o1 instanceof IProgramMethod) && o2 instanceof IProgramMethod) {
                    return 1;
                } else {
                    String s1 = o1.name() instanceof ProgramElementName
                            ? ((ProgramElementName) o1.name()).getProgramName()
                            : o1.name().toString();
                    String s2 = o2.name() instanceof ProgramElementName
                            ? ((ProgramElementName) o2.name()).getProgramName()
                            : o2.name().toString();
                    return s1.compareTo(s2);
                }
            });

            for (IObserverFunction target : targetsArr) {
                Entry te = new Entry(getDisplayName(services, target));
                TreeItem<Entry> childNode = new TreeItem<>(te);
                te.kjt = kjt;
                te.target = target;
                node.getChildren().add(childNode);
            }
        }
    }

    private static void compressLinearPaths(TreeItem<Entry> root) {

        int numChildren = root.getChildren().size();
        for (int i = 0; i < numChildren; i++) {
            TreeItem<Entry> child = root.getChildren().get(i);
            int numGrandChildren = child.getChildren().size();
            if (numGrandChildren == 1) {
                TreeItem<Entry> grandChild = child.getChildren().get(0);
                // stop compressing at method name
                if (grandChild.getValue().target != null) {
                    continue;
                }
                child.getChildren().remove(grandChild);
                root.getChildren().set(i, grandChild);
                Entry e1 = child.getValue();
                Entry e2 = grandChild.getValue();
                e2.string = e1.string + "." + e2.string;
                compressLinearPaths(root);
            }
        }
    }

    /**
     * <p>
     * Returns a human readable display name for the given {@link ObserverFunction} with use of
     * the given {@link Services}.
     * </p>
     * <p>
     * Ported verbatim from {@code ClassTree.getDisplayName} (also used by other products).
     * </p>
     *
     * @param services The {@link Services} to use.
     * @param ov The {@link ObserverFunction} for that a display name is needed.
     * @return The display name for the given {@link ObserverFunction}.
     */
    public static String getDisplayName(Services services, IObserverFunction ov) {
        StringBuilder sb = new StringBuilder();
        String prettyName = HeapLDT.getPrettyFieldName(ov);
        if (prettyName != null) {
            sb.append(prettyName);
        } else if (ov.name() instanceof ProgramElementName) {
            sb.append(((ProgramElementName) ov.name()).getProgramName());
        } else {
            sb.append(ov.name());
        }
        if (ov.getNumParams() > 0 || ov instanceof IProgramMethod) {
            sb.append("(");
        }
        for (KeYJavaType paramType : ov.getParamTypes()) {
            sb.append(paramType.getSort().name()).append(", ");
        }
        if (ov.getNumParams() > 0) {
            sb.setLength(sb.length() - 2);
        }
        if (ov.getNumParams() > 0 || ov instanceof IProgramMethod) {
            sb.append(")");
        }
        return sb.toString();
    }

    private static TreeItem<Entry> createTree(boolean addContractTargets,
            boolean skipLibraryClasses, Services services) {
        // get all classes
        var types = new ArrayList<>(services.getJavaInfo().getAllKeYJavaTypes());
        types.removeIf(kjt -> !(kjt.getJavaType() instanceof ClassDeclaration
                || kjt.getJavaType() instanceof InterfaceDeclaration)
                || (((TypeDeclaration) kjt.getJavaType()).isLibraryClass() && skipLibraryClasses));

        // sort classes alphabetically
        types.sort(Comparator.comparing(KeYJavaType::getFullName));

        // build tree
        TreeItem<Entry> rootNode = new TreeItem<>(new Entry(""));
        for (KeYJavaType keYJavaType : types) {
            insertIntoTree(rootNode, keYJavaType, addContractTargets, services);
        }

        compressLinearPaths(rootNode);
        return rootNode;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Selects the given Java type (and optionally its contract target) and expands the path to
     * it (Swing {@code ClassTree.select} + {@code open}). Inner types are reached via their
     * root type node like in the Swing original.
     *
     * @param kjt the Java type to select
     * @param target the contract target to select, may be {@code null}
     */
    public void select(KeYJavaType kjt, IObserverFunction target) {
        // get tree path to class
        List<TreeItem<Entry>> path = new ArrayList<>();
        TreeItem<Entry> node = getRoot();
        path.add(node);
        // Collect inner classes
        Deque<KeYJavaType> types = new ArrayDeque<>();
        KeYJavaType currentKjt = kjt;
        types.addFirst(currentKjt);
        while (KeYTypeUtil.isInnerType(services, currentKjt)) {
            String parentFullName = KeYTypeUtil.getParentName(services, kjt);
            currentKjt = KeYTypeUtil.getType(services, parentFullName);
            types.addFirst(currentKjt);
        }
        // extend tree path to root class
        Iterator<KeYJavaType> typesIter = types.iterator();
        KeYJavaType rootType = typesIter.next();
        TreeItem<Entry> fullQualifiedNode = searchNode(node, rootType.getFullName());
        if (fullQualifiedNode != null) {
            path.add(fullQualifiedNode);
            node = fullQualifiedNode;
        } else {
            final String[] segments = rootType.getFullName().split("\\.");
            String accumulatedSegment = null;
            for (final String segment : segments) {
                accumulatedSegment =
                    accumulatedSegment == null ? segment : accumulatedSegment + "." + segment;
                final TreeItem<Entry> resNode = searchNode(node, accumulatedSegment);
                if (resNode != null) {
                    node = resNode;
                    path.add(node);
                    accumulatedSegment = null;
                }
            }
        }
        // extend tree path to inner classes
        while (typesIter.hasNext()) {
            KeYJavaType innerType = typesIter.next();
            node = searchNode(node, innerType.getName());
            path.add(node);
        }

        // extend tree path to method
        TreeItem<Entry> methodNode = null;
        if (target != null) {
            methodNode = getChildByTarget(node, target);
        }

        // open and select
        // expand all ancestors of the target node (the Swing code expands the incomplete path)
        for (TreeItem<Entry> item : path) {
            item.setExpanded(true);
        }
        TreeItem<Entry> selection = methodNode != null ? methodNode : node;
        selection.setExpanded(true);
        getSelectionModel().clearSelection();
        getSelectionModel().select(selection);
        scrollTo(getRow(selection));
    }

    /**
     * Selects the given Java type (no contract target).
     *
     * @param kjt the Java type to select
     */
    public void select(KeYJavaType kjt) {
        select(kjt, null);
    }

    /**
     * @return the root node of the tree
     */
    public TreeItem<Entry> getRootNode() {
        return getRoot();
    }

    /**
     * @return the entry of the currently selected node or {@code null} if nothing is selected
     */
    public Entry getSelectedEntry() {
        TreeItem<Entry> node = getSelectionModel().getSelectedItem();
        return node != null ? node.getValue() : null;
    }

    /**
     * Searches the child of {@code parent} with the given text.
     *
     * @param parent the node to search in
     * @param text the text of the child to search for
     * @return the first found child with the given text or {@code null} if there is none
     */
    protected TreeItem<Entry> searchNode(TreeItem<Entry> parent, String text) {
        for (TreeItem<Entry> childNode : parent.getChildren()) {
            Entry e = childNode.getValue();
            if (Objects.equals(text, e.string)) {
                return childNode;
            }
        }
        return null;
    }
}
