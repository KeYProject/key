// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.*;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.incclosure.*;
import de.uka.ilkd.key.proof.reuse.ReusePoint;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

public class Node {
    /** the proof the node belongs to */
    private Proof               proof;

    private Sequent              seq                 = Sequent.EMPTY_SEQUENT;

    private List<Node>           children            = new LinkedList<Node>();

    private Node                 parent              = null;

    private RuleApp              appliedRuleApp;

    private NameRecorder         nameRecorder;

    private SetOfProgramVariable globalProgVars      = SetAsListOfProgramVariable.EMPTY_SET;

    private boolean              closed              = false;

    /** Root sink if this is a root node */
    private BufferSink           rootSink            = null;

    private BufferSink           localSink;

    /** Parent of all sinks on this branch */
    private Sink                 branchSink;

    /** For children.size()>1 this merger will be used */
    private MultiMerger          forkMerger          = null;

    /** contains non-logical content, used for user feedback */
    private NodeInfo             nodeInfo;

    int                          reuseCandidate      = 0;

    private boolean              persistentCandidate = false;

    private ReusePoint           reuseSource;

    int                          serialNr;

    private int                  siblingNr = -1;

    private ListOfRenamingTable  renamings;
    
    /**
     * If the rule base has been extended e.g. by loading a new taclet as
     * lemma or by applying a taclet with an addrule section on this node,
     * then these taclets are stored in this set
     */
    private SetOfNoPosTacletApp  localIntroducedRules = SetAsListOfNoPosTacletApp.EMPTY_SET;
    
    /** creates an empty node that is root and leaf.
     */
    public Node(Proof proof) {
	this.proof = proof;
	rootSink = new BufferSink ( null );
	branchSink = new BranchRestricter ( rootSink );
	((BranchRestricter)branchSink).setNode ( this );
	localSink  = new BufferSink ( branchSink );
        serialNr = proof.getServices().getCounter("nodes").getCountPlusPlus(this);        
        nodeInfo = new NodeInfo(this);
    }

    /** creates a node with the given contents
     */
    public Node(Proof proof, Sequent seq) {
	this ( proof );
	this.seq=seq;
        serialNr = proof.getServices().getCounter("nodes").getCountPlusPlus(this);
    }


    /** creates a node with the given contents, the given collection
     * of children (all elements must be of class Node) and the given
     * parent node.
     */
    public Node(Proof proof, Sequent seq, List<Node> children,
		Node parent, Sink branchSink) {
	this.proof = proof;
	this.seq=seq;	
	this.parent=parent;
	this.branchSink=branchSink;
	localSink = new BufferSink ( branchSink );
	if (children!=null) {this.children=children;}
        serialNr = proof.getServices().getCounter("nodes").getCountPlusPlus(this);
        nodeInfo = new NodeInfo(this);
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
        this.appliedRuleApp = ruleApp;        
    }

    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    public void setNameRecorder(NameRecorder rec) {
        nameRecorder = rec;
    }

    public void setRenamings(ListOfRenamingTable list){
        renamings = list;
    }

    public ListOfRenamingTable getRenamingTable(){
	return renamings;
    }

    public RuleApp getAppliedRuleApp() {
        return appliedRuleApp;
    }
    
    /** Returns the set of NoPosTacletApps at this node */
    public SetOfNoPosTacletApp getNoPosTacletApps() {
	return localIntroducedRules;
    }

    public SetOfProgramVariable getGlobalProgVars() {
	return globalProgVars;
    }

    public void setGlobalProgVars(SetOfProgramVariable progVars) {
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
    public Node commonAncestor ( Node p_node ) {
	if ( root () )
	    return this;
	if ( p_node.root () )
	    return p_node;

	HashSet<Node> paths = new HashSet<Node> ();
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
     * Reserve p_count sinks meant for children and return them. If
     * ultimately more than one sink is needed, the first call to this
     * method MUST have p_count>1.
     */
    public IteratorOfSink reserveSinks ( int p_count ) {
	if ( p_count == 1 && forkMerger == null )
	    return SLListOfSink.EMPTY_LIST.prepend ( branchSink ).iterator ();
	else {
	    int i = 0;

	    if ( forkMerger == null )
		forkMerger = new MultiMerger ( branchSink, p_count, 
                proof().getServices() );
	    else {
		i = forkMerger.getArity ();
		forkMerger.expand ( i + p_count );
	    }

	    IteratorOfSink it = forkMerger.getSinks ();
	    while ( i-- != 0 )
		it.next ();

	    return it;
	}
    }

    /**
     * Remove a possibly existing merger, restore the old state by
     * calling "localSink.reset()". Currently this doesn't really
     * remove the connection between the children sinks and the branch
     * sink.
     */
    public void cutChildrenSinks () {
	if ( forkMerger != null )
	    forkMerger = null;

	resetBranchSink ();
    }

    /**
     * 
     */
    public void resetBranchSink () {
        localSink.reset ();
    }

    public BufferSink insertLocalRootSink () {
        Debug.assertFalse ( forkMerger == null,
                            "insertLocalRootSink() must only be called for " +
                            "nodes with multiple children" );
        
        final BufferSink localRoot = new BufferSink ( null );
        forkMerger.setParent ( localRoot );

        return localRoot;
    }
    
    public void removeLocalRootSink () {
        Debug.assertFalse ( forkMerger == null,
                            "removeLocalRootSink() must only be called for " +
                            "nodes with multiple children" );

        forkMerger.setParent ( branchSink );
    }
        
    /** makes the given node a child of this node.
     */
    public void add(Node child) {
        child.siblingNr = children.size();
	children.add(child);
	child.parent = this;
	proof().fireProofExpanded(this);
    }

    /** removes child/parent relationship between this node and its
     * parent; if this node is root nothing happens.
     */
    public void remove() {
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
    public boolean remove(Node child) {
        proof().fireProofIsBeingPruned(child.parent, child);
	if (children.remove(child)) {
	    child.parent = null;
            
            final ListIterator<Node> it = children.listIterator(child.siblingNr);
            while (it.hasNext()) {
                it.next().siblingNr--;                
            }
            child.siblingNr = -1;
	    proof().fireProofPruned(this, child);
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
	while (!nodesToCheck.isEmpty()) {
	    final Node n = nodesToCheck.removeFirst();
	    if (n.leaf()) {
		leaves.add(n);
	    } else {
		nodesToCheck.addAll(0, n.children);
	    }
	}
    	return leaves;
    }


    /** 
     * returns an iterator for the leaves of the subtree below this
     * node. The computation is called at every call!
     */
    public NodeIterator leavesIterator() {
	return new NodeIterator(leaves().iterator());
    }

    /** returns an iterator for the direct children of this node.
     */
    public NodeIterator childrenIterator() {
	return new NodeIterator(children.iterator());
    }

    /** returns number of children */
    public int childrenCount() {
	return children.size();
    }

    /** returns i-th child */
    public Node child(int i) {
	return (Node)(children.get(i));
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
    
    
    public String name() { // XXX this is called way too often -- cache stuff!

	RuleApp rap = getAppliedRuleApp();
        if (rap == null) {
	    Goal goal = proof().getGoal(this);
	    if ( goal == null
                 || proof ().getUserConstraint ().displayClosed ( this ) )
                return "Closed goal";
            else if(goal.isAutomatic())
                return "OPEN GOAL";
            else
                return "INTERACTIVE GOAL";
        }
        if (rap.rule() == null) return "rule application without rule";

        if (nodeInfo.getFirstStatementString() != null) {
            return nodeInfo.getFirstStatementString();
        }
        
        String text = rap.rule().displayName();       
        if (text == null) { 
            text = "rule without name";
        }
        return text;
    }   
    
    private static Vector<Node> reuseCandidates = new Vector<Node>(20);
    
    public static Iterator<Node> reuseCandidatesIterator() {
        return reuseCandidates.iterator();
    }

    public static int reuseCandidatesNumber() {
        return reuseCandidates.size();
    }

    public void markReuseCandidate() {
       reuseCandidate++;
       reuseCandidates.add(this);
    }
        
    public void markPersistentCandidate() {
       persistentCandidate = true;
    }

    public void unmarkReuseCandidate() {
       if ((reuseCandidate>1) || !persistentCandidate) {
          reuseCandidate--;
          reuseCandidates.remove(this);
       }
    }
    
    public static void clearReuseCandidates() {
       for (Node n : reuseCandidates) {
           n.reuseCandidate = 0;
           n.persistentCandidate = false;
       }
       reuseCandidates = new Vector<Node>(20);
    }
    
    public static void clearReuseCandidates(Proof p) {
        for (Iterator<Node> it = reuseCandidates.iterator(); it.hasNext();) {
            Node n = it.next();
            if (n.proof() == p) it.remove();
        }
    }
    
    public boolean isReuseCandidate() {
       return reuseCandidate>0;
    }
        
    public void setReuseSource(ReusePoint rp) {
       reuseSource = rp;
    }

    public ReusePoint getReuseSource() {
       return reuseSource;
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


    public Constraint getClosureConstraint () {
	return localSink.getConstraint ();
    }

    public void addClosureConstraint ( Constraint c ) {
	localSink.put ( c );
    }

    public void addRestrictedMetavariable ( Metavariable mv ) {
	localSink.addRestriction ( mv );
    }

    public SetOfMetavariable getRestrictedMetavariables () {
	if ( branchSink instanceof Restricter )
	    return ((Restricter)branchSink).getRestrictions ();
	else
	    return SetAsListOfMetavariable.EMPTY_SET;
    }

    public BufferSink getRootSink () {
	return rootSink;
    }

    public Sink getBranchSink () {
	return branchSink;
    }

    /**
     * This is called by "BranchRestricter" to indicate that the
     * subtree below this Node is closed
     */
    public void subtreeCompletelyClosed () {
	proof ().subtreeCompletelyClosed ( this );
    }

    
    public void setClosed() {
	final LinkedList<Node> subTreeNodes = new LinkedList<Node>();
	subTreeNodes.add(this);	
	while (!subTreeNodes.isEmpty()) {
	    final Node n = (Node)subTreeNodes.removeFirst();
	    n.closed = true;	    
	    subTreeNodes.addAll(n.children);
	}
    }

    public boolean isClosed() {
	return closed;
    }

    /**
     * retrieves number of nodes
     */
    public int countNodes() {
	int nodes = 1 + children.size();
	final LinkedList<Node> nodesToAdd = new LinkedList<Node>(children);
	while (!nodesToAdd.isEmpty()) {
	    final Node n = nodesToAdd.removeFirst();
	    nodesToAdd.addAll(n.children);
	    nodes += n.children.size();
	}
	return nodes;
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
   

    // inner iterator class 
    public static class NodeIterator implements Iterator<Node>, IteratorOfNode {
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

    private int getIntroducedRulesCount() {
        int c = 0;

        if (parent != null) {
            c = parent.getIntroducedRulesCount();
        }

        return c + localIntroducedRules.size();
    }

    public int getUniqueTacletNr() {
        return getIntroducedRulesCount();
    }

 }
