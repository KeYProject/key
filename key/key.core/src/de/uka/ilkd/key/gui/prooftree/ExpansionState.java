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

package de.uka.ilkd.key.gui.prooftree;


/*
http://www.chka.de/swing/tree/expansion/ExpansionState.java
This code is provided by Christian Kaufhold <ch-kaufhold@gmx.de> under LGPL
*/


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.*;

import javax.swing.JTree;
import javax.swing.event.TreeExpansionEvent;
import javax.swing.event.TreeExpansionListener;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;


/** Cache/Access JTree's expansion state. The interface of JTree to access
    the expanded paths is rather incomplete, since expanded paths under
    collapsed ancestors cannot be accessed at all (without modifying the
    expansion states, which doesn't work with vetos of TreeWillExpand-
    Listeners). By listening to TreeExpansionEvents, this class mirrors
    the expansion state for each path individually, independent from that
    of its ancestors. It also listens to the TreeModel to remove paths
    that have become invalid.
    ExpansionStates are serializable if the TreePaths themselves are,
    which they are if their components are. Typically you will want to
    only serialize the state(), which doesn't also serialize the JTree
    (If you wanted to serialize the JTree, you wouldn't need to the state
    for serialization purposes at all.)
    

    There are two ways to use this class:

    a) always have a ExpansionState around. Then the results will always be
       completely right (and always accessible without a lot of overhead).

       Serializing/exporting:
       
           Collection state = cache.state(new HashSet());

           out.writeObject(state);

       When reading the state and creating the JTree, a new ExpansionState
       is created:

           Set state = (Set)in.readObject();

           JTree tree = new JTree(data);

           ExpansionState cache = new ExpansionState(tree, state);

       Actually I don't like the side-effect of the constructor.

       .<Collections>nil() can of course be used if there is no state yet.

    b) Only request the state on demand, and also restore it. This has less overhead
       during execution, but a) has to modify the expansion structure while
       trying to build the state, b) may actually confuse it
       due to vetoes of TreeWillExpandListeners, and c) may give wrong results for
       the same reason.

       Serializing/exporting:

           out.writeObject(ExpansionState.paths(tree, new HashSet()));

       Reading the state:

           Set state = (Set)in.readObject();

           JTree tree = new JTree(data);

           ExpansionState.setPaths(tree, state);

    Note the example code uses HashSet because setPaths() does (and very probably
    always will) make use of contains(), which should thus be fast.
*/
public class ExpansionState
    extends AbstractSet
    implements Serializable
{
    /**
     * 
     */
    private static final long serialVersionUID = -8276873816625710215L;

    private JTree tree;

    private Set paths;

    private transient Listener listener;

    /** For the given JTree. Assumes only the root is expanded, if at all
        (for example, a freshly created JTree, or one for which the model has
        just been set)
     */
    public ExpansionState(JTree t)
    {
        tree = t;
        
        paths = new LinkedHashSet();

        listener = createListener();

        tree.addPropertyChangeListener(listener);
        tree.addTreeExpansionListener(listener);

        TreeModel data = tree.getModel();

        if (data != null)
        {
            data.addTreeModelListener(listener);

            readFromTree();
        }
    }

    /** For the given JTree, with the given set of expanded paths.
        This is equivalent to using the normal constructor, and then
        calling setPaths(tree, state).
    */
    public ExpansionState(JTree tree, Collection state)
    {
        this(tree, state, false);
    }

    /** For the given JTree, with the given set of expanded paths.
        This is equivalent to using the normal constructor, and then
        calling setPaths(tree, state, false);
    */
    public ExpansionState(JTree tree, Collection state, boolean assumeCollapsed)
    {
        this(tree);

        setPaths(tree, state, assumeCollapsed);
    }
    
    public void disconnect(JTree t) {
        tree.removePropertyChangeListener(listener);
        tree.removeTreeExpansionListener(listener);
        TreeModel data = tree.getModel();
        if (data != null) data.removeTreeModelListener(listener);
    }

    private void readFromTree()
    {
        TreeModel data = tree.getModel();

        Object root = data.getRoot();
        
        if (root != null)
        {
            TreePath rootPath = new TreePath(root);
            
            // This is a heuristic, we cannot truly capture all
            // Unless someone has subclassed JTree, only the root
            // will be expanded, if at all.
            // It is much too expensive to really use paths()
            // from below.

            if (tree.isExpanded(rootPath))
                for (Enumeration e = tree.getExpandedDescendants(rootPath); e.hasMoreElements();)
                    paths.add(e.nextElement());
        }
    }


    public int size()
    {
        return paths.size();
    }

    public boolean isEmpty()
    {
        return paths.isEmpty();
    }

    public boolean contains(Object item)
    {
        return paths.contains(item);
    }

    public boolean containsAll(Collection c)
    {
        return paths.containsAll(c);
    }

    /**
       Are all the ancestors (including the path) expanded?
    */
    public boolean containsAncestors(TreePath path)
    {
        do
        {
            if (!contains(path))
                return false;

            path = path.getParentPath();

        } while (path != null);

        return true;
    }

    /**
       Are all the ancestors (including the paths) expanded?
    */
    public boolean containsAllAncestors(Collection c)
    {
        for (Object aC : c)
            if (!containsAncestors((TreePath) aC))
                return false;

        return true;
    }


    public Iterator iterator()
    {
        return new Iterator()
        {
            Iterator i = paths.iterator();

            public boolean hasNext()
            {
                return i.hasNext();
            }

            public Object next()
            {
                return i.next();
            }
            
            public void remove()
            {
                throw new UnsupportedOperationException();
            }
        };
    }



    protected Object clone()
        throws CloneNotSupportedException
    {
        throw new CloneNotSupportedException();
    }


    private void readObject(ObjectInputStream in)
        throws IOException, ClassNotFoundException
    {
        in.defaultReadObject();

        listener = createListener();

        tree.addPropertyChangeListener(listener);
        tree.addTreeExpansionListener(listener);

        TreeModel data = tree.getModel();

        if (data != null)
        {
            data.addTreeModelListener(listener);

            readFromTree();
        }
    }


    public Collection state(Collection result)
    {
        result.clear();
        result.addAll(paths);

        return result;
    }

    
    /** Will re-expand the root if it was expanded and the tree has
        an invisible root (otherwise the tree will appear empty, and there
        is no easy way for the user to change that.
    */
    public static void collapseAll(JTree tree)
    {
        TreeModel data = tree.getModel();

        if (data == null)
            return;

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root))
            return;

        TreePath rootPath = new TreePath(root);

        boolean rootExpanded = tree.isExpanded(rootPath);

        collapseAll(tree, rootPath);

        if (rootExpanded && !tree.isRootVisible())
            tree.expandPath(rootPath);
    }

    /** requires: root is not a leaf. That implies that the tree's model is
        not null and does have a root.
     */
    public static void collapseAll(JTree tree, TreePath root)
    {
        collapseAllImpl(tree, tree.getModel(), root);
    }

    private static void collapseAllImpl(JTree tree, TreeModel data, TreePath path)
    {
        Object node = path.getLastPathComponent();

        for (int count = data.getChildCount(node), i = 0; i < count; i++)
        {
            Object child = data.getChild(node, i);

            if (!data.isLeaf(child))
                collapseAllImpl(tree, data, path.pathByAddingChild(child));
        }

        // cannot check, since we cannot assume all ancestors
        // are expanded
        // afterwards they are, though, so the first walk could be handled
        // special?
        tree.collapsePath(path);
    }


    public static void expandAll(JTree tree)
    {
        TreeModel data = tree.getModel();

        if (data == null)
            return;

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root))
            return;

        expandAll(tree, new TreePath(root));
    }

    /** requires: path is not a leaf. That implies the tree has a model,
        and that has a root.
    */
    public static void expandAll(JTree tree, TreePath path)
    {
        for (Object o : extremalPaths(tree.getModel(), path, new LinkedHashSet())) tree.expandPath((TreePath) o);
    }


    /** The "extremal paths" of the tree model's subtree starting at
        path. The extremal paths are those paths that a) are non-leaves
        and b) have only leaf children, if any. It suffices to know
        these to know all non-leaf paths in the subtree, and those are
        the ones that matter for expansion (since the concept of expan-
        sion only applies to non-leaves).
        The extremal paths collection of a leave is empty.
        The extremal paths are stored in the order in which they appear
        in pre-order in the tree model.
    */
    private static Collection extremalPaths(TreeModel data, TreePath path, Collection result)
    {
        result.clear();

        if (data.isLeaf(path.getLastPathComponent()))
            return result; // should really be forbidden (?)
        
        extremalPathsImpl(data, path, result);

        return result;
    }

    private static void extremalPathsImpl(TreeModel data, TreePath path, Collection result)
    {
        Object node = path.getLastPathComponent();
        
        boolean hasNonLeafChildren = false;

        int count = data.getChildCount(node);
        
        for (int i = 0; i < count; i++)
            if (!data.isLeaf(data.getChild(node, i)))
                hasNonLeafChildren = true;

        if (!hasNonLeafChildren)
            result.add(path);
        else
        {
            for (int i = 0; i < count; i++)
            {
                Object child = data.getChild(node, i);
                
                if (!data.isLeaf(child))
                    extremalPathsImpl(data, path.pathByAddingChild(child), result);
            }
        }
    }


    


    
    /** All paths in the JTree that are expanded, including those 
        under hidden parents. The result is the same as if attaching
        an ExpansionState to the JTree (in creation state) and then
        calling state() on it.
        To return the proper result, this method must temporarily
        expand paths. If any TreeWillExpandListeners veto that, the
        result is undefined.
    */
    public static Collection paths(JTree tree, Collection result)
    {
        result.clear();

        TreeModel data = tree.getModel();

        if (data == null)
            return result;

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root))
            return result;

        pathsImpl(tree, data, new TreePath(root), result);

        return result;
    }

    private static void pathsImpl(JTree tree, TreeModel data, TreePath path, Collection result)
    {
        boolean expanded = tree.isExpanded(path);

        if (expanded)
            result.add(path);
        else
            tree.expandPath(path);

        Object node = path.getLastPathComponent();

        for (int count = data.getChildCount(node), i = 0; i < count; i++)
        {
            Object child = data.getChild(node, i);

            if (!data.isLeaf(child))
                pathsImpl(tree, data, path.pathByAddingChild(child), result);
        }

        if (!expanded)
            tree.collapsePath(path);
    }


    /** Try to expand exactly the paths given in paths. Of course requires them to be
        valid in the current TreeModel.
        Will give undefined results if any TreeWillExpandListeners veto.
        This implementation does not assume all paths are collapsed.
     */
    public static void setPaths(JTree tree, Collection paths)
    {
        setPaths(tree, paths, false);
    }

    /** assumedCollapsed: if true, assume that (if at all) only the root
        is expanded. That way, the iteration over the tree nodes only goes
        to the maximum level of the nodes in 'paths'.
    */
    public static void setPaths(JTree tree, Collection paths, boolean assumeCollapsed)
    {
        TreeModel data = tree.getModel();
        
        if (data == null)
            return;

        Object root = data.getRoot();

        if (root == null || data.isLeaf(root))
            return;

        if (assumeCollapsed)
        {
            int maxLevel = 1; // always handle the root (doesn't really matter)

            for (Object path : paths) maxLevel = Math.max(maxLevel, ((TreePath) path).getPathCount());

            setPathsImpl(tree, data, new TreePath(root), maxLevel - 1, paths);
        }
        else
            setPathsImpl(tree, data, new TreePath(root), Integer.MAX_VALUE, paths);
    }

    private static void setPathsImpl(JTree tree, TreeModel data, TreePath path, int maxLevel, Collection paths)
    {
        if (maxLevel > 0)
        {
            Object node = path.getLastPathComponent();
            
            for (int count = data.getChildCount(node), i = 0; i < count; i++)
            {
                Object child = data.getChild(node, i);

                if (!data.isLeaf(child))
                    setPathsImpl(tree, data, path.pathByAddingChild(child), maxLevel - 1, paths);
            }
        }
        
        // Since this is post-order, it doesn't matter that the ancestors are
        // also expanded. They will be handled afterwards.
        if (paths.contains(path))
        {
            if (!tree.isExpanded(path))
                tree.expandPath(path);
        }
        else
        {
            // The ancestors are always expanded, so isCollapse() won't give
            // wrong results.
            if (!tree.isCollapsed(path))
                tree.collapsePath(path);
        }
    }



    private Listener createListener()
    {
        return new Listener();
    }

    private class Listener
        implements TreeExpansionListener, TreeModelListener,
                   PropertyChangeListener
    {
        public void propertyChange(PropertyChangeEvent e)
        {
            if (e.getPropertyName().equals("model"))
            {
                TreeModel old = (TreeModel)e.getOldValue();

                if (old != null)
                    old.removeTreeModelListener(this);

                paths.clear();

                TreeModel data = tree.getModel();
                
                if (data != null)
                {
                    data.addTreeModelListener(this);
                    readFromTree();
                }
            }
        }

        public void treeExpanded(TreeExpansionEvent e)
        {
            paths.add(e.getPath());
        }

        public void treeCollapsed(TreeExpansionEvent e)
        {
            paths.remove(e.getPath());
        }
 
        public void treeNodesChanged(TreeModelEvent e)
        {
        }

        public void treeNodesInserted(TreeModelEvent e)
        {
        }

        public void treeNodesRemoved(TreeModelEvent e)
        {
            TreePath parent = e.getTreePath();

            Object[] children = e.getChildren();

            for (Object aChildren : children) removeDescendants(parent.pathByAddingChild(aChildren));
        }

        public void treeStructureChanged(TreeModelEvent e)
        {
            TreePath path = e.getTreePath();


            // Heuristic for new null root. It is undocumented which
            // event really to expect.
            if (path == null)
            {
                paths.clear();
                return;
            }
            
            // new root, or root changed. JTree will maybe expand the root.
            if (path.getParentPath() == null)
            {
                paths.clear();
                readFromTree();
            }
            else
            {
                removeDescendants(path);

		// PR
		if ( tree.isExpanded ( path ) )
		    paths.add(path);
            }
        }

        // remove the descendants (which, by definition, include the path
        // itself)
        private void removeDescendants(TreePath path)
        {
            for (Iterator i = paths.iterator(); i.hasNext();)
            {
                TreePath current = (TreePath)i.next();

                if (current.isDescendant(path))
                    i.remove();
            }
        }
    }
}