/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;


/*
 * http://www.chka.de/swing/tree/expansion/ExpansionState.java This code is provided by Christian
 * Kaufhold <ch-kaufhold@gmx.de> under LGPL
 */

import java.util.*;
import java.util.function.Predicate;
import javax.annotation.Nonnull;
import javax.swing.JTree;
import javax.swing.event.*;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;


/**
 * Cache/Access JTree's expansion state. The interface of JTree to access the expanded paths is
 * rather incomplete, since expanded paths under collapsed ancestors cannot be accessed at all
 * (without modifying the expansion states, which doesn't work with vetos of TreeWillExpand-
 * Listeners). By listening to TreeExpansionEvents, this class mirrors the expansion state for each
 * path individually, independent from that of its ancestors. It also listens to the TreeModel to
 * remove paths that have become invalid. ExpansionStates are serializable if the TreePaths
 * themselves are, which they are if their components are. Typically you will want to only serialize
 * the state(), which doesn't also serialize the JTree (If you wanted to serialize the JTree, you
 * wouldn't need to the state for serialization purposes at all.)
 *
 * There are two ways to use this class:
 *
 * a) always have a ExpansionState around. Then the results will always be completely right (and
 * always accessible without a lot of overhead).
 *
 * Serializing/exporting:
 *
 * Collection state = cache.state(new HashSet());
 *
 * out.writeObject(state);
 *
 * When reading the state and creating the JTree, a new ExpansionState is created:
 *
 * Set state = (Set)in.readObject();
 *
 * JTree tree = new JTree(data);
 *
 * ExpansionState cache = new ExpansionState(tree, state);
 *
 * Actually I don't like the side-effect of the constructor.
 *
 * .<Collections>nil() can of course be used if there is no state yet.
 *
 * b) Only request the state on demand, and also restore it. This has less overhead during
 * execution, but a) has to modify the expansion structure while trying to build the state, b) may
 * actually confuse it due to vetoes of TreeWillExpandListeners, and c) may give wrong results for
 * the same reason.
 *
 * Serializing/exporting:
 *
 * out.writeObject(ExpansionState.paths(tree, new HashSet()));
 *
 * Reading the state:
 *
 * Set state = (Set)in.readObject();
 *
 * JTree tree = new JTree(data);
 *
 * ExpansionState.setPaths(tree, state);
 *
 * Note the example code uses HashSet because setPaths() does (and very probably always will) make
 * use of contains(), which should thus be fast.
 *
 * <p>
 * Note: For optimization purposes, this class is now tailored to ProofTreeView. In particular, the
 * method {@link #expandAllBelow(JTree, TreePath, Predicate)} temporarily removes most
 * TreeExpansionListeners to avoid flooding them with events. This massively increases performance
 * on large trees.
 * <p>
 * Note: The current implementation probably does not work correctly with TreeWillExpandListeners.
 *
 * @author Wolfram Pfeifer: optimized, migrated from older Java version, renamed, and tailored to
 *         ProofTreeView, removed unnecessary serialization stuff and unused code
 */
class ProofTreeExpansionState extends AbstractSet<TreePath> {

    /** the JTree of the ProofTreeView */
    private final @Nonnull JTree tree;

    /**
     * Stores all paths that are currently expanded. This includes those which are hidden because
     * some of their parents are collapsed. All paths not in this set are collapsed.
     *
     * @implNote We always use a LinkedHashSet now since this makes the path traversal order
     *           predictable.
     */
    private final @Nonnull Set<TreePath> paths = new LinkedHashSet<>();

    /** Listens for changes in the proof tree as well as for expansion/collapse of GUI nodes. */
    private final @Nonnull Listener listener = new Listener();

    /**
     * For the given JTree. Assumes only the root is expanded, if at all (for example, a freshly
     * created JTree, or one for which the model has just been set)
     *
     * @param t the JTree of the ProofTreeView
     */
    public ProofTreeExpansionState(@Nonnull JTree t) {
        tree = t;
        tree.addTreeExpansionListener(listener);

        TreeModel data = tree.getModel();

        if (data != null) {
            data.addTreeModelListener(listener);

            // readFromTree();
            // could be tuned even further by avoiding copying the set, however, even the largest
            // proofs have only a couple of hundreds entries in paths, so this is negligible ...
            paths.addAll(paths(tree));
        }
    }

    /**
     * Creates a new ProofExpansionState for the given JTree, where the given paths are expanded
     * initially.
     *
     * @param tree the JTree this ProofExpansionState refers to
     * @param state the collection of paths to expand initially
     */
    public ProofTreeExpansionState(@Nonnull JTree tree, @Nonnull Collection<TreePath> state) {
        this(tree);
        setPaths(tree, state);
    }

    /**
     * Reads the current expansion state from the assigned tree and updates the set of expanded
     * paths. Note that the set should be empty when calling the method. Instead of
     * <code>readFromTree()</code> now the following should be used:
     *
     * <code>paths.clear();<br>
     *       paths.addAll(paths(tree));</code>
     *
     * @deprecated Since paths() has been made much more efficient while it is also more precise in
     *             some cases, it should be used instead. However, we still keep this method around
     *             in case performance problems with paths() occur in the future.
     */
    @Deprecated
    private void readFromTree() {
        TreeModel data = tree.getModel();

        Object root = data.getRoot();

        if (root != null) {
            TreePath rootPath = new TreePath(root);

            // This is a heuristic, we cannot truly capture all
            // Unless someone has subclassed JTree, only the root
            // will be expanded, if at all.
            // It is much too expensive to really use paths()
            // from below.

            if (tree.isExpanded(rootPath)) {
                for (Enumeration<TreePath> e = tree.getExpandedDescendants(rootPath); e
                        .hasMoreElements();) {
                    paths.add(e.nextElement());
                }
            }
        }
    }

    /**
     * Disconnects the ProofTreeExpansionState from the associated JTree. This means that it no
     * longer listens for tree expansions.
     */
    public void disconnect() {
        tree.removeTreeExpansionListener(listener);
        TreeModel data = tree.getModel();
        if (data != null) {
            data.removeTreeModelListener(listener);
        }
    }

    @Override
    public int size() {
        return paths.size();
    }

    @Override
    public boolean isEmpty() {
        return paths.isEmpty();
    }

    @Override
    public boolean contains(Object item) {
        return paths.contains(item);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return paths.containsAll(c);
    }

    @Override
    public Iterator<TreePath> iterator() {
        return new Iterator<>() {
            final Iterator<TreePath> i = paths.iterator();

            @Override
            public boolean hasNext() {
                return i.hasNext();
            }

            @Override
            public TreePath next() {
                return i.next();
            }
        };
    }

    @Override
    protected Object clone() throws CloneNotSupportedException {
        throw new CloneNotSupportedException();
    }

    /**
     * Copies the currently stored expansion state of the associated tree.
     *
     * @return a shallow copy of the collection of expanded paths
     */
    public @Nonnull Collection<TreePath> copyState() {
        // we need a copy here, such that the set is not shared between multiple trees!
        return new LinkedHashSet<>(paths);
    }

    /**
     * Collapses all paths of the tree. However, it re-expands the root if it was expanded before
     * and the tree has an invisible root, since otherwise the tree will appear empty, and there is
     * no easy way for the user to change that.
     *
     * @param tree the JTree to collapse
     */
    public static void collapseAll(JTree tree) {
        TreeModel data = tree.getModel();

        if (data == null) {
            return;
        }

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root)) {
            return;
        }

        TreePath rootPath = new TreePath(root);

        boolean rootExpanded = tree.isExpanded(rootPath);

        collapseAllBelow(tree, rootPath);

        if (rootExpanded && !tree.isRootVisible()) {
            tree.expandPath(rootPath);
        }
    }

    /**
     * Collapses all nodes that are below the given path. Requires that the given path is not a
     * leaf. That implies that the tree's model is not null and does have a root.
     *
     * @param tree the JTree to collapse
     * @param path the path which will be collapsed afterwards (including all children recursively)
     */
    public static void collapseAllBelow(JTree tree, TreePath path) {
        Object node = path.getLastPathComponent();
        TreeModel data = tree.getModel();

        for (int count = data.getChildCount(node), i = 0; i < count; i++) {
            Object child = data.getChild(node, i);

            if (!data.isLeaf(child)) {
                collapseAllBelow(tree, path.pathByAddingChild(child));
            }
        }

        // cannot check, since we cannot assume all ancestors
        // are expanded
        // afterwards they are, though, so the first walk could be handled
        // special?
        tree.collapsePath(path);
    }


    /**
     * Expands the given JTree completely.
     *
     * Expands the given JTree completely except for the filtered out nodes.
     *
     * @param tree the JTree to expand
     * @param filter only the nodes that pass this filter will be expanded
     */
    public static void expandAll(JTree tree, Predicate<TreePath> filter) {
        TreeModel data = tree.getModel();

        if (data == null) {
            return;
        }

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root)) {
            return;
        }

        expandAllBelow(tree, new TreePath(root), filter);
    }

    /**
     * Completely expands all nodes of the given JTree that are below the given path and pass the
     * given filter. Requires that path is not a leaf. That implies the tree has a model, and that
     * has a root.
     *
     * @param tree the JTree to expand
     * @param path the root path under which everything should be expanded afterwards
     * @param filter only the nodes that pass this filter will be expanded
     */
    public static void expandAllBelow(JTree tree, TreePath path, Predicate<TreePath> filter) {
        // we temporarily remove all expansion listeners (except that which updates the expanded
        // paths set) before expanding
        TreeExpansionListener[] expansionListeners = tree.getTreeExpansionListeners();
        for (TreeExpansionListener exl : expansionListeners) {
            if (!(exl instanceof Listener)) {
                tree.removeTreeExpansionListener(exl);
            }
        }
        for (TreePath tp : extremalPaths(tree.getModel(), path, filter)) {
            tree.expandPath(tp);
        }
        for (TreeExpansionListener exl : expansionListeners) {
            if (!(exl instanceof Listener)) {
                tree.addTreeExpansionListener(exl);
            }
        }
        // inform the listeners for drawing
        tree.fireTreeExpanded(path);
    }


    /**
     * The "extremal paths" of the tree model's subtree starting at path. The extremal paths are
     * those paths that a) are non-leaves and b) have only leaf children, if any. It suffices to
     * know these to know all non-leaf paths in the subtree, and those are the ones that matter for
     * expansion (since the concept of expan- sion only applies to non-leaves). The extremal paths
     * collection of a leave is empty. The extremal paths are stored in the order in which they
     * appear in pre-order in the tree model.
     */
    private static Collection<TreePath> extremalPaths(TreeModel data, TreePath path,
            Predicate<TreePath> filter) {
        LinkedHashSet<TreePath> result = new LinkedHashSet<>();

        if (data.isLeaf(path.getLastPathComponent())) {
            return result; // should really be forbidden (?)
        }

        extremalPathsImpl(data, path, result, filter);
        return result;
    }

    private static void extremalPathsImpl(TreeModel data, TreePath path,
            Collection<TreePath> result, Predicate<TreePath> filter) {
        Object node = path.getLastPathComponent();

        boolean hasNonLeafChildren = false;

        int count = data.getChildCount(node);

        // check if there is a child that is not leaf and passes the filter
        for (int i = 0; i < count; i++) {
            Object child = data.getChild(node, i);
            if (!data.isLeaf(child) && filter.test(path.pathByAddingChild(child))) {
                hasNonLeafChildren = true;
                break;
            }
        }

        if (!hasNonLeafChildren) {
            // filtered out nodes (e.g. OSS nodes) must not be expanded
            if (filter.test(path)) {
                result.add(path);
            }
        } else {
            for (int i = 0; i < count; i++) {
                Object child = data.getChild(node, i);

                if (!data.isLeaf(child)) {
                    extremalPathsImpl(data, path.pathByAddingChild(child), result, filter);
                }
            }
        }
    }

    /**
     * All paths in the JTree that are expanded, including those under hidden parents. The result is
     * the same as if attaching a ProofTreeExpansionState to the JTree (in creation state) and then
     * calling getState() on it. To return the proper result, this method must temporarily expand
     * paths. If any TreeWillExpandListeners veto that, the result is undefined.
     *
     * @param tree the JTree the expanded paths are read from
     * @return the TreePaths that are currently expanded in the given tree, even if any of their
     *         parents are collapsed
     */
    public static Collection<TreePath> paths(JTree tree) {
        Collection<TreePath> result = new LinkedHashSet<>();

        TreeModel data = tree.getModel();

        if (data == null) {
            return result;
        }

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root)) {
            return result;
        }

        /*
         * To avoid unnecessary events caused by temporary expansion, we disable the listeners. This
         * makes the method an order of a magnitude faster for large proofs.
         */
        TreeExpansionListener[] treeExpansionListeners = tree.getTreeExpansionListeners();
        for (TreeExpansionListener tel : treeExpansionListeners) {
            tree.removeTreeExpansionListener(tel);
        }

        pathsImpl(tree, data, new TreePath(root), result);

        // reenable listeners
        for (TreeExpansionListener tel : treeExpansionListeners) {
            tree.addTreeExpansionListener(tel);
        }

        return result;
    }

    private static void pathsImpl(JTree tree, TreeModel data, TreePath path,
            Collection<TreePath> result) {
        boolean expanded = tree.isExpanded(path);

        if (expanded) {
            result.add(path);
        } else {
            tree.expandPath(path);
        }

        Object node = path.getLastPathComponent();

        for (int count = data.getChildCount(node), i = 0; i < count; i++) {
            Object child = data.getChild(node, i);

            if (!data.isLeaf(child)) {
                pathsImpl(tree, data, path.pathByAddingChild(child), result);
            }
        }

        if (!expanded) {
            tree.collapsePath(path);
        }
    }


    /**
     * Try to expand exactly the given paths given in paths (assumes them to be valid in the current
     * TreeModel). Will give undefined results if any TreeWillExpandListeners veto.
     *
     * @param tree the JTree where exactly the paths should be expanded
     * @param paths the paths to expand. All other paths will be collapsed. Note that collapsed
     *        parent paths may hide their children, even if those are expanded.
     */
    public static void setPaths(@Nonnull JTree tree, @Nonnull Collection<TreePath> paths) {
        TreeModel data = tree.getModel();

        if (data == null) {
            return;
        }

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root)) {
            return;
        }

        // temporarily disable the listeners to avoid flooding them with events
        TreeExpansionListener[] expansionListeners = tree.getTreeExpansionListeners();
        for (TreeExpansionListener exl : expansionListeners) {
            if (!(exl instanceof Listener)) {
                tree.removeTreeExpansionListener(exl);
            }
        }

        setPathsImpl(tree, data, new TreePath(root), Integer.MAX_VALUE, paths);

        // reenable listeners
        for (TreeExpansionListener exl : expansionListeners) {
            if (!(exl instanceof Listener)) {
                tree.addTreeExpansionListener(exl);
            }
        }

        // inform the listeners for redrawing
        tree.fireTreeExpanded(new TreePath(root));
    }

    private static void setPathsImpl(@Nonnull JTree tree, @Nonnull TreeModel data,
            @Nonnull TreePath start, int maxLevel, @Nonnull Collection<TreePath> paths) {
        // only expand up to depth maxLevel starting from the given start path
        if (maxLevel > 0) {
            Object node = start.getLastPathComponent();

            for (int count = data.getChildCount(node), i = 0; i < count; i++) {
                Object child = data.getChild(node, i);

                if (!data.isLeaf(child)) {
                    setPathsImpl(tree, data, start.pathByAddingChild(child), maxLevel - 1, paths);
                }
            }
        }

        // Since this is post-order, it doesn't matter that the ancestors are
        // also expanded. They will be handled afterwards.
        if (paths.contains(start)) {
            if (!tree.isExpanded(start)) {
                tree.expandPath(start);
            }
        } else {
            // The ancestors are always expanded, so isCollapse() won't give
            // wrong results.
            if (!tree.isCollapsed(start)) {
                tree.collapsePath(start);
            }
        }
    }

    private class Listener implements TreeExpansionListener, TreeModelListener {
        @Override
        public void treeExpanded(TreeExpansionEvent e) {
            paths.add(e.getPath());
        }

        @Override
        public void treeCollapsed(TreeExpansionEvent e) {
            paths.remove(e.getPath());
        }

        @Override
        public void treeNodesChanged(TreeModelEvent e) {
        }

        @Override
        public void treeNodesInserted(TreeModelEvent e) {
        }

        @Override
        public void treeNodesRemoved(TreeModelEvent e) {
            // TODO: this code seems to be never called, since GUIProofTreeModel only
            // fires treeStructureChanged events
            TreePath parent = e.getTreePath();

            Object[] children = e.getChildren();

            for (Object aChildren : children) {
                removeDescendants(parent.pathByAddingChild(aChildren));
            }
        }

        @Override
        public void treeStructureChanged(TreeModelEvent e) {
            TreePath path = e.getTreePath();

            // Heuristic for new null root. It is undocumented which
            // event really to expect.
            if (path == null) {
                paths.clear();
                return;
            }

            // new root, or root changed. JTree will maybe expand the root.
            if (path.getParentPath() == null) {
                // readFromTree();
                paths.clear();
                paths.addAll(paths(tree));
            } else {
                removeDescendants(path);

                if (tree.isExpanded(path)) {
                    paths.add(path);
                }
            }
        }

        // remove the descendants (which, by definition, include the path itself)
        private void removeDescendants(TreePath path) {
            paths.removeIf(current -> current.isDescendant(path));
        }
    }
}
