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

import java.util.Collection;
import java.util.Collections;
import java.util.Stack;
import java.util.WeakHashMap;

import javax.swing.event.EventListenerList;
import javax.swing.event.TreeModelEvent;
import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;


import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter.NodeFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.util.Debug;

/** An implementation of TreeModel that can be displayed using the
 * JTree class framework and reflects the state of a
 * {@link de.uka.ilkd.key.proof.Proof} object.
 *
 * <p>The tree structure of the proof is transformed, so that nodes
 * following each other on a long branch are represented as kin, while
 * new sutrees are displayed for branching points.
 *
 * <p>There are thus two kinds of node in this TreeModel,
 * {@link de.uka.ilkd.key.gui.prooftree.GUIProofTreeNode}s, representing nodes of
 * the displayed proof, and {@link de.uka.ilkd.key.gui.prooftree.GUIBranchNode}s
 * representing branching points.  (There is also one at the root.)
 */

class GUIProofTreeModel implements TreeModel, java.io.Serializable  {

	private static final long serialVersionUID = 4253914848471158358L;
	private Proof proof;
    private ProofTreeListener proofTreeListener;
    private NodeFilter activeNodeFilter = null;

    private EventListenerList listenerList = new EventListenerList();

    private boolean attentive = true;


    /** construct a GUIProofTreeModel that mirrors the given
     * Proof.
     */
    public GUIProofTreeModel(Proof p) {
        if (p == null) {
            throw new IllegalArgumentException("null proof in "
                    +"GUIProofTreeModel().");
        }
        this.proof = p;
        proofTreeListener = new ProofTreeListener();

        // set initial active node filter
        for (ProofTreeViewFilter f: ProofTreeViewFilter.ALL) {
            if (f instanceof NodeFilter && f.isActive())
                activeNodeFilter = (NodeFilter)f;
        }
    }

   class ProofTreeListener extends ProofTreeAdapter {

      private Node pruningInProcess;

      public void proofStructureChanged(ProofTreeEvent e) {
        if (pruningInProcess != null) return;
        Node n = e.getNode();
         // we assume that there already is a "node" event for every other
         // type of event
         if (n != null) {
	     updateTree(getProofTreeNode(n));
             return;
         }

         Goal g = e.getGoal();
         if (g != null) {
	     updateTree(getProofTreeNode(g.node()));
             }

      }

      public void proofIsBeingPruned(ProofTreeEvent e){
            pruningInProcess = e.getNode();
      }

      /** The proof tree under the node mentioned in the ProofTreeEvent
       * is in pruning phase. The subtree of node will be removed after this
       * call but at this point the subtree can still be
       * traversed (e.g. in order to free the nodes in caches).
       * The method proofPruned is called, when the nodes are disconnect from
       * node.
       */
      public void proofPruned(ProofTreeEvent e){
              updateTree(getProofTreeNode(pruningInProcess));
              pruningInProcess = null;
      }

      public void proofGoalRemoved (ProofTreeEvent e) {
              if (pruningInProcess != null) return;
              if ( hideClosedSubtrees () ) {
                      updateTree((TreeNode) null);
              } else
                      proofStructureChanged ( e );
      }

   }



    /** Call this when the GUIProofTreeModel is no longer needed.
     * GUIProofTreeModel registers a Listener with its associated
     * Proof object.  This method unregisters that listener, which is
     * a good thing, as the proof maintains a reference to the
     * listener, and the listener to the GUIProofTreeModel, so it would
     * never become GC'ed unless you call this method.
     *
     * <p>Note that after calling <code>unregister</code>, this
     * GUIProofTreeModel does not respond to changes in the proof tree
     * any more.
     */
    public void unregister() {
	proof.removeProofTreeListener(proofTreeListener);
    }

    public void register() {
	proof.addProofTreeListener(proofTreeListener);
    }


    /** Sets whether this object should respond to changes in the
     * the proof immediately. */
    public void setAttentive(boolean b) {
	Debug.out("setAttentive:", b);
	if ( b != attentive && !proof.isDisposed()) {
	    if ( b ) {
		proof.addProofTreeListener(proofTreeListener);
		//		updateTree(null);
                if ( hideClosedSubtrees () ) {
                    updateTree((TreeNode) null);
                }
	    } else {
		proof.removeProofTreeListener(proofTreeListener);
	    }
	    attentive = b;
	}
    }

    /** returns true if the model respond to changes in the proof
     * immediately */
    public boolean isAttentive() {
	return attentive;
    }

    /**
     * Adds a listener for the TreeModelEvent posted after the tree changes.
     * Such events are generated whenever the underlying Proof changes.
     *
     * @see     #removeTreeModelListener
     * @param   l       the listener to add
     */
    public void addTreeModelListener(TreeModelListener l) {
	listenerList.add(TreeModelListener.class, l);
    }

    /**
     * Removes a listener previously added with <B>addTreeModelListener()</B>.
     *
     * @see     #addTreeModelListener
     * @param   l       the listener to remove
     */
    public void removeTreeModelListener(TreeModelListener l) {
	listenerList.remove(TreeModelListener.class, l);
    }


    public boolean hideClosedSubtrees () {
        return ProofTreeViewFilter.HIDE_CLOSED_SUBTREES.isActive();
    }

    /**
     * Set filters active or inactive and update tree if necessary.
     * @param filter
     * @param active
     */
    public void setFilter (ProofTreeViewFilter filter, boolean active) {
        if (active != filter.isActive()) {
            if (!filter.global()) {
                if (activeNodeFilter != null)
                    activeNodeFilter.setActive(false);
                activeNodeFilter = active? (NodeFilter)filter: null;
            }
            filter.setActive(active);
            updateTree((TreeNode) null);
        }
    }

    /**
     * Returns the child of <I>parent</I> at index <I>index</I> in the parent's
     * child array.  <I>parent</I> must be a node previously obtained from
     * this data source. This should not return null if <i>index</i>
     * is a valid index for <i>parent</i> (that is <i>index</i> >= 0 &&
     * <i>index</i> < getChildCount(<i>parent</i>)).
     *
     * @param   parent  a node in the tree, obtained from this data source
     * @return  the child of <I>parent</I> at index <I>index</I>
     */
    public Object getChild(Object parent, int index) {
        if (activeNodeFilter == null) {
            TreeNode guiParent = (TreeNode)parent;
            if (guiParent.getChildCount()>index) {
                return guiParent.getChildAt(index);
            }
        } else {
            return activeNodeFilter.getChild(parent, index);
        }
        return null;
    }

    /**
     * Returns the number of children of <I>parent</I>.  Returns 0 if the node
     * is a leaf or if it has no children.  <I>parent</I> must be a node
     * previously obtained from this data source.
     *
     * @param   parent  a node in the tree, obtained from this data source
     * @return  the number of children of the node <I>parent</I>
     */
    public int getChildCount(Object parent) {
        if (activeNodeFilter == null) {
            return ((TreeNode) parent).getChildCount();
        } else {
            return activeNodeFilter.getChildCount(parent);
        }
    }

    /**
     * Returns the index of child in parent.
     *
     * @param   parent  a node in the tree, obtained from this data source
     * @param   child  a child of parent, obtained from this data source
     * @return  The index of child in parent

     */
    public int getIndexOfChild(Object parent, Object child) {
        TreeNode guiParent = (TreeNode)parent;
        if (activeNodeFilter == null) {
            for (int i = 0; i < guiParent.getChildCount();i++) {
                if (guiParent.getChildAt(i) == child) {
                    return i;
                }
            }
        } else {
            return activeNodeFilter.getIndexOfChild(parent, child);
        }
        return -1;
    }

    /**
     * Returns the root of the tree.  Returns null only if the tree has
     * no nodes.
     *
     * @return  the root of the tree
     */
    public Object getRoot() {
	return getBranchNode(proof.root(),"Proof Tree");
    }

    /**
     * Returns true if <I>node</I> is a leaf.  It is possible for this method
     * to return false even if <I>node</I> has no children.  A directory in a
     * filesystem, for example, may contain no files; the node representing
     * the directory is not a leaf, but it also has no children.
     *
     * @param   guiNode a node in the tree, obtained from this data source
     * @return  true if <I>node</I> is a leaf
     */
    public boolean isLeaf(Object guiNode){
	return ((TreeNode)guiNode).isLeaf();
    }

    /**
      * Messaged when the user has altered the value for the item identified
      * by <I>path</I> to <I>newValue</I>.  We throw an exception,
      * as proofs are not meant to be chaged via the JTree editing facility.
      *
      * @param path path to the node that the user has altered.
      * @param newValue the new value from the TreeCellEditor.
      */
    public void valueForPathChanged(TreePath path, Object newValue) {
	if (path.getLastPathComponent() instanceof GUIBranchNode) {
	    ((GUIBranchNode)path.getLastPathComponent()).setLabel((String)newValue);
	}
    }


    /**
     * Take the appropriate actions after a change in the Proof.
     * Currently, this means throwing all cached Information away
     * and fire an indiscriminating TreeStructureChanged event.
     * This should probably be made more efficient.
     *
     * @param trn tree node to update.
     */
    private void updateTree(TreeNode trn) {
        if (trn == null || trn == getRoot()) { // bigger change, redraw whole tree
	    proofTreeNodes = new WeakHashMap<Node, GUIAbstractTreeNode>();
	    branchNodes    = new WeakHashMap<Node, GUIBranchNode>();
            fireTreeStructureChanged(new Object[]{getRoot()});
            return;
        }
        // otherwise redraw only a certain subtree
        // starting from the parent of trn
        flushCaches ( trn );
        // also flush the current node, it might be an OSS conceiving children in this step
        ((GUIAbstractTreeNode)trn).flushCache();
        TreeNode[] path = ((GUIAbstractTreeNode)trn.getParent()).getPath();
        fireTreeStructureChanged(path);
    }

    public void updateTree(Node p_node) {
        if ( p_node == null ) {
            updateTree ( (TreeNode)null );
        } else {
            updateTree ( getProofTreeNode ( p_node ) );
        }
    }

    private void flushCaches (TreeNode trn) {
        Node n = ( (GUIAbstractTreeNode)trn ).getNode ();
        while ( true ) {
            final Node p = n.parent ();
            if ( p == null ||( (GUIAbstractTreeNode)trn ).findChild(p) == null ) break;
            n = p;
        }

        flushCaches ( n );
    }

    private void flushCaches(Node n) {
        final Stack<Node> workingList = new Stack<Node> ();
        workingList.add ( n );
        while ( !workingList.empty () ) {
            Node node = workingList.pop ();
            final GUIBranchNode treeNode = findBranch ( node );
            if ( treeNode == null ) continue;
            treeNode.flushCache ();
            while ( true ) {
                final Node nextN = treeNode.findChild(node);
                if ( nextN == null ) break;
                node = nextN;
            }

            for ( int i = 0; i != node.childrenCount (); ++i )
                if (!treeNode.getProofTreeModel().hideClosedSubtrees() ||
                	!node.child ( i ).isClosed () )
                workingList.add ( node.child ( i ) );
        }
    }

    /** Notify all listeners that have registered interest for
     * notification on treeStructureChanged events.
     */
    protected void fireTreeStructureChanged(Object[] path) {
	TreeModelEvent event = null;
	// Guaranteed to return a non-null array
	Object[] listeners = listenerList.getListenerList();
	// Process the listeners last to first, notifying
	// those that are interested in this event
	for (int i = listeners.length-2; i>=0; i-=2) {
	    if (listeners[i]==TreeModelListener.class) {
		// Lazily create the event:
		if (event == null)
		    event = new TreeModelEvent(this, path);
		((TreeModelListener)listeners[i+1])
		    .treeStructureChanged(event);
	    }
	}
    }

    // caches for the GUIProofTreeNode and GUIBranchNode objects
    // generated to represent the nodes resp. subtrees of the Proof.

    private WeakHashMap<Node, GUIAbstractTreeNode> proofTreeNodes = new WeakHashMap<Node, GUIAbstractTreeNode>();
    private WeakHashMap<Node, GUIBranchNode> branchNodes    = new WeakHashMap<Node, GUIBranchNode>();

    /** Return the GUIProofTreeNode corresponding to node n, if one
     * has already been generated, and null otherwise.
     */
    public GUIAbstractTreeNode find(Node n) {
	return (proofTreeNodes.get(n));
    }

    /** Return the GUIProofTreeNode corresponding to node n.
     * Generate one if necessary.
     */
    public GUIAbstractTreeNode getProofTreeNode(Node n) {
 	GUIAbstractTreeNode res = find(n);
	if ( res == null ) {
	    res = new GUIProofTreeNode(this,n);
	    proofTreeNodes.put(n,res);
	}
	return res;
    }

    /**
     * Return the GUIBranchNode corresponding to the subtree rooted
     * at n, if one has already been generated, and null otherwise.
     */
    public GUIBranchNode findBranch(Node n) {
	return branchNodes.get(n);
    }

    /**
     * Return the GUIBranchNode corresponding to the subtree rooted
     * at n.  Generate one if necessary, using label as the the
     * subtree label.
     */
    public GUIBranchNode getBranchNode(Node n,
				       Object label) {
 	GUIBranchNode res = findBranch(n);
	if ( res == null ) {
	    res = new GUIBranchNode(this,n,label);
	    branchNodes.put(n,res);
	}
	return res;
    }



    Collection expansionState = Collections.EMPTY_SET;

    public void storeExpansionState(Collection c) {
       expansionState = c;
//System.err.println("Proof "+proof.name()+" stor. state: "+ expansionState   );
    }

    public Collection getExpansionState() {
//System.err.println("Proof "+proof.name()+" retr. state: "+ expansionState   );
       return expansionState;
    }

    TreePath selection;

    public void storeSelection(TreePath t) {
        selection = t;
    }

    public TreePath getSelection() {
        return selection;
    }

}
