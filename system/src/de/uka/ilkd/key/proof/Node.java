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

package de.uka.ilkd.key.proof;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;

public class Node  {
    private static final String RULE_WITHOUT_NAME = "rule without name";

    private static final String RULE_APPLICATION_WITHOUT_RULE = "rule application without rule";

    private static final String INTERACTIVE_GOAL = "INTERACTIVE GOAL";

    private static final String OPEN_GOAL = "OPEN GOAL";

    private static final String CLOSED_GOAL = "Closed goal";

    private static final String NODES = "nodes";

    /** the proof the node belongs to */
    private final Proof               proof;

    private Sequent              seq                 = Sequent.EMPTY_SEQUENT;

    private ArrayList<Node>      children            = new ArrayList<Node>(1);

    private Node                 parent              = null;

    private RuleApp              appliedRuleApp;

    private NameRecorder         nameRecorder;

    private ImmutableSet<ProgramVariable> globalProgVars      = DefaultImmutableSet.<ProgramVariable>nil();

    private boolean              closed              = false;

    /** contains non-logical content, used for user feedback */
    private final NodeInfo             nodeInfo;

    private final int                  serialNr;

    private int                  siblingNr = -1;

    private ImmutableList<RenamingTable>  renamings;

    private String cachedName = null;

    /**
     * If the rule base has been extended e.g. by loading a new taclet as
     * lemma or by applying a taclet with an addrule section on this node,
     * then these taclets are stored in this list
     */
    private ImmutableSet<NoPosTacletApp>  localIntroducedRules =
            DefaultImmutableSet.<NoPosTacletApp>nil();

    /**
     * Holds the undo methods for the information added by rules to the
     * {@link Goal#strategyInfos}.
     */
    private List<StrategyInfoUndoMethod>  undoInfoForStrategyInfo =
            new ArrayList<StrategyInfoUndoMethod>();

    /** creates an empty node that is root and leaf.
     */

    public Node(Proof proof) {
	this.proof = proof;
        serialNr = proof.getServices().getCounter(NODES).getCountPlusPlus();
        nodeInfo = new NodeInfo(this);
    }

    /** creates a node with the given contents
     */
    public Node(Proof proof, Sequent seq) {
	this ( proof );
	this.seq=seq;
    }


    /** creates a node with the given contents, the given collection
     * of children (all elements must be of class Node) and the given
     * parent node.
     */
    public Node(Proof proof, Sequent seq, Node parent) {
        this(proof, seq);
        this.parent=parent;
    }

    /** sets the sequent at this node
     */
    public void setSequent(Sequent seq) {
	this.seq=seq;
   }

    /** returns the sequent of this node */
    public Sequent sequent() {
	return seq;
    }

    /**
     * the node information object encapsulates non-logical information
     * of the node, e.g.
     *
     * @return the NodeInfo containing non-logical information
     */
    public NodeInfo getNodeInfo() {
        return nodeInfo;
    }

    /** returns the proof the Node belongs to */
    public Proof proof() {
	return proof;
    }

    public void setAppliedRuleApp(RuleApp ruleApp) {
        this.nodeInfo.updateNoteInfo();
        this.appliedRuleApp = ruleApp;
        clearNameCache();
    }

    public void clearNameCache() {
        cachedName = null;
    }

    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    public void setNameRecorder(NameRecorder rec) {
        nameRecorder = rec;
    }

    public void setRenamings(ImmutableList<RenamingTable> list){
        renamings = list;
    }

    public ImmutableList<RenamingTable> getRenamingTable(){
	return renamings;
    }

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }

    /** Returns the set of NoPosTacletApps at this node */
    public Iterable<NoPosTacletApp> getLocalIntroducedRules() {
	return localIntroducedRules;
    }

    public ImmutableSet<ProgramVariable> getGlobalProgVars() {
	return globalProgVars;
    }

    public void setGlobalProgVars(ImmutableSet<ProgramVariable> progVars) {
	globalProgVars=progVars;
    }

     /**
      * adds a new NoPosTacletApp to the set of available NoPosTacletApps
      * at this node
      */
     public void addNoPosTacletApp(NoPosTacletApp s) {
 	localIntroducedRules = localIntroducedRules.add(s);
     }

    /** returns the parent node of this node.
     */
    public Node parent() {
	return parent;
    }

    /** returns true, iff this node is a leaf, i.e. has no children.
     */
    public boolean leaf() {
	return children.size()==0;
    }

    /** searches for a given node in the subtree starting with this node */
    public boolean find(Node node) {
	// we assume that the proof tree node is part of has proper
	// links

	while ( node != this ) {
	    if ( node.root () )
		return false;
	    node = node.parent ();
	}

	return true;
    }

    /**
     * Search for the node being the root of the smallest subtree
     * containing <code>this</code> and <code>p_node</code>; we assume
     * that the two nodes are part of the same proof tree
     */
    // XXX this method is never used
    public Node commonAncestor ( Node p_node ) {
	if ( root () )
	    return this;
	if ( p_node.root () )
	    return p_node;

	HashSet<Node> paths = new LinkedHashSet<Node> ();
	Node    n     = this;

	while ( true ) {
	    if ( !paths.add ( n ) )
		return n;
	    if ( n.root () )
		break;
	    n = n.parent ();

	    if ( !paths.add ( p_node ) )
		return p_node;
	    if ( p_node.root () ) {
		p_node = n;
		break;
	    }
	    p_node = p_node.parent ();
	}

	while ( !paths.contains ( p_node ) )
	    p_node = p_node.parent ();

	return p_node;
    }

    /**  returns true, iff this node is root, i.e. has no parents.
     */
    public boolean root() {
	return parent==null;
    }

    /**
     *  makes the given node a child of this node.
     */
    public void add(Node child) {
        child.siblingNr = children.size();
        children.add(child);
        child.parent = this;
        proof().fireProofExpanded(this);
    }

    /**
     *  makes the given node a child of this node.
     */
    public void addAll(Node[] newChildren) {
        final int size = children.size();
        for (int i = 0; i<newChildren.length; i++) {
            newChildren[i].siblingNr = i + size; 
            newChildren[i].parent = this;
        }        
        
        Collections.addAll(children, newChildren);
        children.trimToSize();
        
        proof().fireProofExpanded(this);
    }
    
    
    
    /** removes child/parent relationship between this node and its
     * parent; if this node is root nothing happens.
     * This is only used for testing purposes.
     */
    void remove() {
	if (parent != null) {
	    parent.remove(this);
	}
    }

    /** removes child/parent relationship between the given node and
     * this node; if the given node is not child of this node,
     * nothing happens and then and only then false is returned.
     * @return false iff the given node was not child of this node and
     * nothing has been done.
     */
    boolean remove(Node child) {
	if (children.remove(child)) {
	    child.parent = null;
            final ListIterator<Node> it = children.listIterator(child.siblingNr);
            while (it.hasNext()) {
                it.next().siblingNr--;
            }
            child.siblingNr = -1;
	    return true;
	} else {
	    return false;
	}
    }


    /**
     * computes the leaves of the current subtree and returns them
     */
    private List<Node> leaves() {
	final List<Node> leaves = new LinkedList<Node>();
	final LinkedList<Node> nodesToCheck = new LinkedList<Node>();
	nodesToCheck.add(this);
	do {
	    final Node n = nodesToCheck.poll();
	    if (n.leaf()) {
		leaves.add(n);
	    } else {
		nodesToCheck.addAll(0, n.children);
	    }
	} while (!nodesToCheck.isEmpty());
    	return leaves;
    }


    /**
     * returns an iterator for the leaves of the subtree below this
     * node. The computation is called at every call!
     */
    public Iterator<Node> leavesIterator() {
	return new NodeIterator(leaves().iterator());
    }

    /** returns an iterator for the direct children of this node.
     */
    public Iterator<Node> childrenIterator() {
	return new NodeIterator(children.iterator());
    }

    /** returns an iterator for all nodes in the subtree.
     */
    public Iterator<Node> subtreeIterator() {
        return new SubtreeIterator(this);
    }

    /** returns number of children */
    public int childrenCount() {
	return children.size();
    }

    /** returns i-th child */
    public Node child(int i) {
	return children.get(i);
    }

    /**
     * @return the number of the node <code>p_node</code>, if it is a
     * child of this node (starting with <code>0</code>),
     * <code>-1</code> otherwise
     */
    public int getChildNr ( Node p_node ) {
	int            res = 0;
	final Iterator<Node> it  = childrenIterator ();

	while ( it.hasNext () ) {
	    if ( it.next () == p_node )
		return res;
	    ++res;
	}

	return -1;
    }

    public StringBuffer getUniqueTacletId() {
        StringBuffer id = new StringBuffer();
        int c = 0;
        Node n = this;

        while (n != null) {
            c += n.localIntroducedRules.size();
                      
            if (n.parent != null && n.parent.childrenCount() > 1) {
               id.append(n.siblingNr);
            }
            
            n = n.parent;
        }    
        
        id.append("_").append(c);
        
        return id;
    }

    
    /** helps toString method
     * @param prefix needed to keep track if a line has to be printed
     * @param tree the tree representation we want to add this subtree
     " @param preEnumeration the enumeration of the parent without the
     * last number
     * @param postNr the last number of the parents enumeration
     * @param maxNr the number of nodes at this level
     * @param ownNr the place of this node at this level
     */

    private StringBuffer toString(String prefix,
				  StringBuffer tree,
				  String preEnumeration,
				  int postNr,
				  int maxNr,
				  int ownNr
				  ) {
	Iterator<Node> childrenIt = childrenIterator();
	// Some constants
	String frontIndent=(maxNr>1 ? " " : "");
	String backFill="   "; // same length as connectNode without
			       // frontIndent
	String connectNode=(maxNr>1 ? frontIndent+"+--" : "");
	String verticalLine=(maxNr>1 ? frontIndent+"|"+backFill : " |");


	// get enumeration
	String newEnumeration=preEnumeration;
	int newPostNr=0;
	if (maxNr>1) {
	    newEnumeration+=postNr+"."+ownNr+".";
	    newPostNr=1;
	} else {
	    newPostNr=postNr+ownNr;
	}

	// node is printed

	if (postNr!=0) { // not starting node (usually not root)
	    // prefix is appended twice in order to get an
	    // empty line between two nodes
	    tree.append(prefix);
	    tree.append(verticalLine);
	    tree.append("\n");
       	    tree.append(prefix);
	    // indent node
	    tree.append(connectNode);
	}

	tree.append("("+newEnumeration+newPostNr+") "+sequent().toString()+"\n");

	// create new prefix
	if (ownNr<maxNr) {
	    // connect node with next node of same level
	    prefix+=verticalLine;
	} else if (ownNr==maxNr && maxNr>1) {
	    // last node of level no further connection
	    prefix+=frontIndent+" "+backFill;
	} else if (ownNr!=maxNr && maxNr<=1) {
	    prefix="";
	}

	// print subtrees
	int childId=0;
	while (childrenIt.hasNext()) {
	    childId++;
	    childrenIt.next().toString(prefix, tree, newEnumeration,
				       newPostNr,
				       children.size(), childId);
	}

	return tree;
    }


    public String toString() {
	StringBuffer tree=new StringBuffer();
	return "\n"+toString("",tree,"",0,0,1);
    }


    public String name() {
        if (cachedName == null) {

            RuleApp rap = getAppliedRuleApp();
            if (rap == null) {
                Goal goal = proof().getGoal(this);
                if ( goal == null || this.isClosed() )
                    return CLOSED_GOAL; // don't cache this
                else if(goal.isAutomatic())
                    cachedName = OPEN_GOAL;
                else
                    cachedName = INTERACTIVE_GOAL;
                return cachedName;
            }
            if (rap.rule() == null) {
                cachedName = RULE_APPLICATION_WITHOUT_RULE;
                return cachedName;
            }

            if (nodeInfo.getFirstStatementString() != null) {
                return nodeInfo.getFirstStatementString();
            }

            cachedName = rap.rule().displayName();
            if (cachedName == null) {
                cachedName = RULE_WITHOUT_NAME;
            }
        }
        return cachedName;
    }


    /**
     * checks if the parent has this node as child and continues recursively
     * with the children of this node.
     * @return true iff the parent of this node has this node as child and
     * this condition holds also for the own children.
     */
    public boolean sanityCheckDoubleLinks() {
	if (!root()) {
	    if (!parent().children.contains(this)) {
		return false;
	    }
	    if (parent.proof() != proof()) {
		return false;
	    }
	}
	if (!leaf()) {
	    final Iterator<Node> it = childrenIterator();
	    while (it.hasNext()) {
		if (!it.next().sanityCheckDoubleLinks())
		    return false;
	    }
	}
	return true;
    }


    /** marks a node as closed */
    Node close() {
        closed = true;
        Node tmp = parent;
        Node result = this;
        while (tmp != null && tmp.isCloseable()) {
            tmp.closed = true;
            result = tmp;
            tmp = tmp.parent();
        }
        clearNameCache();
        return result;
    }

    /** checks if an inner node is closeable */
    private boolean isCloseable() {
	assert childrenCount() > 0;
	for (Node child: children) {
	    if ( !child.isClosed() ) {
		return false;
	    }
	}
	return true;
    }

    public boolean isClosed() {
	return closed;
    }

    /**
     * retrieves number of nodes
     */
    public int countNodes() {
        Iterator<Node> it = subtreeIterator();
        int res = 0;
        for (; it.hasNext(); it.next()) res++;
        return res;
    }

    /**
     * retrieves number of branches
     */
    public int countBranches() {
	return leaves().size();
    }

    public int serialNr() {
        return serialNr;
    }

    /**
     * returns the sibling number of this node or <tt>-1</tt> if
     * it is the root node
     * @return the sibling number of this node or <tt>-1</tt> if
     * it is the root node
     */
    public int siblingNr() {
        return siblingNr;
    }

    public List<StrategyInfoUndoMethod> getStrategyInfoUndoMethods() {
        return undoInfoForStrategyInfo;
    }

    public void addStrategyInfoUndoMethod(StrategyInfoUndoMethod undoMethod) {
        undoInfoForStrategyInfo.add(undoMethod);
    }

    /** Iterator over children.
     * Use <code>leavesIterator()</code> if you need to iterate over leaves instead.
     */
    public Iterator<Node> iterator() {
        return childrenIterator();
    }

    // inner iterator class
    private static class NodeIterator implements Iterator<Node> {
	private Iterator<Node> it;

	NodeIterator(Iterator<Node> it) {
	    this.it=it;
	}

	public boolean hasNext() {
	    return it.hasNext();
	}

	public Node next() {
	    return it.next();
	}

	public void remove() {
	    throw new UnsupportedOperationException("Changing the proof tree " +
	    		"structure this way is not allowed.");
	}
    }

    /** Iterator over subtree.
     * Current implementation iteratively traverses the tree depth-first.
     * @author bruns
     */
    private static class SubtreeIterator implements Iterator<Node> {
        private Node n;
        private boolean atRoot = true; // special handle

        private SubtreeIterator(Node root) {
            assert root != null;
            n = root;
        }

        private static Node nextSibling(Node m) {
            Node p = m.parent;
            while (p != null) {
                final int c = p.childrenCount();
                final int x = p.getChildNr(m);
                if (x+1 < c) return p.child(x+1);
                m = p; p = m.parent;
            }
            return null;
        }

        @Override
        public boolean hasNext(){
            if (atRoot) return true;
            if (!n.leaf()) return true;
            return nextSibling(n) != null;
        }

        @Override
        public Node next() {
            if (atRoot) { // stay at root once
                atRoot = false;
                return n;
            }
            if (n.leaf()) {
                Node s = nextSibling(n);
                if (s != null) n = s;
            } else n = n.child(0);
            return n;
        }
        
        public void remove() {
            throw new UnsupportedOperationException("Changing the proof tree " +
                    "structure this way is not allowed.");
        }
    }
}