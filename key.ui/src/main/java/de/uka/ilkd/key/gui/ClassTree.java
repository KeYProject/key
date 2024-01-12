/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.tree.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableSet;


public class ClassTree extends JTree {

    /**
     *
     */
    private static final long serialVersionUID = -3006761219011776834L;
    private final Map<Pair<KeYJavaType, IObserverFunction>, Icon> targetIcons;
    private final Services services;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ClassTree(boolean addContractTargets, boolean skipLibraryClasses, Services services,
            Map<Pair<KeYJavaType, IObserverFunction>, Icon> targetIcons) {
        super(new DefaultTreeModel(createTree(addContractTargets, skipLibraryClasses, services)));
        this.targetIcons = targetIcons;
        this.services = services;
        getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        setCellRenderer(new DefaultTreeCellRenderer() {
            /**
             *
             */
            private static final long serialVersionUID = -6609972972532204432L;

            public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel,
                    boolean expanded, boolean leaf, int row, boolean hasFocus) {
                DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
                Entry entry = (Entry) node.getUserObject();

                Component result;
                if (entry.target == null) {
                    result = super.getTreeCellRendererComponent(tree, value, sel, expanded, true,
                        row, hasFocus);
                } else {
                    result = super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf,
                        row, hasFocus);

                    if (result instanceof JLabel) {
                        ((JLabel) result).setIcon(ClassTree.this.targetIcons.get(
                            new Pair<>(entry.kjt, entry.target)));
                    }
                }

                return result;
            }
        });
    }


    public ClassTree(boolean addContractTargets, boolean skipLibraryClasses, Services services) {
        this(addContractTargets, skipLibraryClasses, services,
            new LinkedHashMap<>());
    }



    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private static DefaultMutableTreeNode getChildByString(DefaultMutableTreeNode parentNode,
            String childString) {
        int numChildren = parentNode.getChildCount();
        for (int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode = (DefaultMutableTreeNode) (parentNode.getChildAt(i));

            Entry te = (Entry) (childNode.getUserObject());
            if (childString.equals(te.string)) {
                return childNode;
            }
        }
        return null;
    }


    private static DefaultMutableTreeNode getChildByTarget(DefaultMutableTreeNode parentNode,
            IObserverFunction target) {
        int numChildren = parentNode.getChildCount();
        for (int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode childNode = (DefaultMutableTreeNode) (parentNode.getChildAt(i));

            Entry te = (Entry) (childNode.getUserObject());
            if (target.equals(te.target)) {
                return childNode;
            }
        }
        return null;
    }


    private static void insertIntoTree(DefaultMutableTreeNode rootNode, KeYJavaType kjt,
            boolean addContractTargets, Services services) {
        String fullClassName = kjt.getFullName();
        int length = fullClassName.length();
        int index = -1;
        DefaultMutableTreeNode node = rootNode;
        do {
            // get next part of the name
            int lastIndex = index;
            index = fullClassName.indexOf('.', ++index);
            if (index == -1) {
                index = length;
            }
            String namePart = fullClassName.substring(lastIndex + 1, index);

            // try to get child node; otherwise, create and insert it
            DefaultMutableTreeNode childNode = getChildByString(node, namePart);
            if (childNode == null) {
                Entry te = new Entry(namePart);
                childNode = new DefaultMutableTreeNode(te);
                node.add(childNode);
            }

            // go down to child node
            node = childNode;
        } while (index != length);

        // save kjt in leaf
        ((Entry) node.getUserObject()).kjt = kjt;

        // add all contract targets of kjt
        if (addContractTargets) {
            final ImmutableSet<IObserverFunction> targets =
                services.getSpecificationRepository().getContractTargets(kjt);

            // sort targets alphabetically
            final IObserverFunction[] targetsArr =
                targets.toArray(new IObserverFunction[targets.size()]);
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
                DefaultMutableTreeNode childNode = new DefaultMutableTreeNode(te);
                te.kjt = kjt;
                te.target = target;
                node.add(childNode);
            }
        }
    }


    private static void compressLinearPaths(DefaultMutableTreeNode root) {

        int numChildren = root.getChildCount();
        for (int i = 0; i < numChildren; i++) {
            DefaultMutableTreeNode child = (DefaultMutableTreeNode) root.getChildAt(i);
            int numGrandChildren = child.getChildCount();
            if (numGrandChildren == 1) {
                DefaultMutableTreeNode grandChild = (DefaultMutableTreeNode) child.getFirstChild();
                // stop compressing at method name
                if (((Entry) grandChild.getUserObject()).target != null) {
                    continue;
                }
                child.removeFromParent();
                root.add(grandChild);
                Entry e1 = (Entry) child.getUserObject();
                Entry e2 = (Entry) grandChild.getUserObject();
                e2.string = e1.string + "." + e2.string;
                compressLinearPaths(root);
            }
        }
    }



    /**
     * <p>
     * Returns a human readable display name for the given {@link ObserverFunction} with use of the
     * given {@link Services}.
     * </p>
     * <p>
     * This functionality is also required by other products and is for that reason available as
     * static utility method.
     * </p>
     *
     * @param services The {@link Services} to use.
     * @param ov The {@link ObserverFunction} for that a display name is needed.
     * @return The display name for the given {@link ObserverFunction}.
     */
    public static final String getDisplayName(Services services, IObserverFunction ov) {
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


    private static DefaultMutableTreeNode createTree(boolean addContractTargets,
            boolean skipLibraryClasses, Services services) {
        // get all classes
        final Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
        kjts.removeIf(kjt -> !(kjt.getJavaType() instanceof ClassDeclaration
                || kjt.getJavaType() instanceof InterfaceDeclaration)
                || (((TypeDeclaration) kjt.getJavaType()).isLibraryClass()
                        && skipLibraryClasses));

        // sort classes alphabetically
        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[0]);
        Arrays.sort(kjtsarr, Comparator.comparing(KeYJavaType::getFullName));

        // build tree
        DefaultMutableTreeNode rootNode = new DefaultMutableTreeNode(new Entry(""));
        for (KeYJavaType keYJavaType : kjtsarr) {
            insertIntoTree(rootNode, keYJavaType, addContractTargets, services);
        }

        compressLinearPaths(rootNode);
        return rootNode;
    }


    private void open(KeYJavaType kjt, IObserverFunction target) {
        // get tree path to class
        ArrayList<DefaultMutableTreeNode> pathVector = new ArrayList<>();
        DefaultMutableTreeNode node = (DefaultMutableTreeNode) getModel().getRoot();
        assert node != null;
        pathVector.add(node);
        // Collect inner classes
        Deque<KeYJavaType> types = new LinkedList<>();
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
        DefaultMutableTreeNode fullQualifiedNode = searchNode(node, rootType.getFullName());
        if (fullQualifiedNode != null) {
            pathVector.add(fullQualifiedNode);
            node = fullQualifiedNode;
        } else {
            final String[] segments = rootType.getFullName().split("\\.");
            String accumulatedSegment = null;
            for (final String segment : segments) {
                accumulatedSegment =
                    accumulatedSegment == null ? segment : accumulatedSegment + "." + segment;
                final DefaultMutableTreeNode resNode = searchNode(node, accumulatedSegment);
                if (resNode != null) {
                    node = resNode;
                    pathVector.add(node);
                    accumulatedSegment = null;
                }
            }
        }
        // extend tree path to inner classes
        while (typesIter.hasNext()) {
            KeYJavaType innerType = typesIter.next();
            node = searchNode(node, innerType.getName());
            pathVector.add(node);
        }
        TreePath path = new TreePath(pathVector.toArray());
        TreePath incompletePath = null;

        // extend tree path to method
        if (target != null) {
            DefaultMutableTreeNode methodNode = getChildByTarget(node, target);
            if (methodNode != null) {
                incompletePath = path;
                path = path.pathByAddingChild(methodNode);
            } else {
                incompletePath = path.getParentPath();
            }
        }

        // open and select
        expandPath(incompletePath);
        setSelectionRow(getRowForPath(path));
    }

    /**
     * Searches the {@link DefaultMutableTreeNode} child with the given text.
     *
     * @param parent The {@link DefaultMutableTreeNode} to search in.
     * @param text The text of the {@link DefaultMutableTreeNode} to search.
     * @return The first found {@link DefaultMutableTreeNode} with the given text or {@code null} if
     *         no {@link DefaultMutableTreeNode} was found.
     */
    protected DefaultMutableTreeNode searchNode(DefaultMutableTreeNode parent, String text) {
        for (int i = 0; i < parent.getChildCount(); i++) {
            DefaultMutableTreeNode childNode = (DefaultMutableTreeNode) parent.getChildAt(i);
            Entry e = (Entry) childNode.getUserObject();

            if (Objects.equals(text, e.string)) {
                return childNode;
            }
        }
        return null;
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public void select(KeYJavaType kjt) {
        open(kjt, null);
    }


    public void select(KeYJavaType kjt, IObserverFunction target) {
        open(kjt, target);
    }


    public DefaultMutableTreeNode getRootNode() {
        return (DefaultMutableTreeNode) getModel().getRoot();
    }


    public DefaultMutableTreeNode getSelectedNode() {
        TreePath path = getSelectionPath();
        return path != null ? (DefaultMutableTreeNode) path.getLastPathComponent() : null;
    }


    public Entry getSelectedEntry() {
        DefaultMutableTreeNode node = getSelectedNode();
        return node != null ? (Entry) node.getUserObject() : null;
    }



    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    static class Entry {
        public String string;
        public KeYJavaType kjt = null;
        public IObserverFunction target = null;
        public int numMembers = 0;
        public int numSelectedMembers = 0;

        public Entry(String string) {
            this.string = string;
        }

        public String toString() {
            return string;
        }
    }
}
