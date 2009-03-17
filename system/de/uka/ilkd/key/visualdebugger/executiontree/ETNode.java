package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.*;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.SLListOfNode;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.DebuggerPO;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;

/**
 * A node of an execution tree representing the control flow of a program.
 * 
 * 
 * FIXME: the copy method creates insane trees (I do currently no understand
 * what ITNodes are, but most probably the copy method brings ETNodes and
 * ITNodes out of sync), up to now I am not sure which behaviour of copy has
 * been wanted. This bug applies to all subclasses as well.
 */
public class ETNode {
    
    /** The children. */
    private LinkedList<ETNode> children = new LinkedList<ETNode>();

    /** The last method invocation. */
    private ETMethodInvocationNode lastMethodInvocation = null;

    /** The last expression start. */
    private ETStatementNode lastExpressionStart = null;

    /** The parent. */
    private ETNode parent = null;

    /** The mediator. */
    private KeYMediator mediator = VisualDebugger.getVisualDebugger()
            .getMediator();

    /** The bc. */
    private ListOfTerm bc = SLListOfTerm.EMPTY_LIST;
    
    /** A list of watchpoints satisfied at this node. */
    private List<WatchPoint> watchpointsSatisfied = null;
    
    /** Indicates that the watchpoint has been true for a subset of nodes of the proof tree nodes. */
    private Set<WatchPoint> watchpointsTrueInSubset = new HashSet<WatchPoint>();

    // ListOfTerm pc= SLListOfTerm.EMPTY_LIST;
    /** The it nodes. */
    private LinkedList<ITNode> itNodes = new LinkedList<ITNode>();

    /** The nobc. */
    private boolean nobc = false;
    
    /** If true the border of this node will be painted green, indicating that this node is collapsed. */
    private boolean isCollapsed = false;
    
    /** True, if at least one watchpoint is satisfied at this node. If true the border of this node will be painted yellow. */
    private boolean isWatchpoint = false;
    
    /** The simplified bc. */
    private ListOfTerm simplifiedBC = null;

    /**
     * Instantiates a new eT node.
     * 
     * @param bc the bc
     * @param parent the parent
     */
    public ETNode(ListOfTerm bc, ETNode parent) {
        this.bc = bc;
        this.parent = parent;
        this.setMethodInvocation();
    }

    /**
     * Instantiates a new eT node.
     * 
     * @param bc the bc
     * @param itNodes the it nodes
     * @param parent the parent
     */
    public ETNode(ListOfTerm bc, LinkedList<ITNode> itNodes, ETNode parent) {
        this.bc = bc;
        this.itNodes = itNodes;
        this.parent = parent;
        this.setMethodInvocation();
    }

    /**
     * Sets the method invocation.
     */
    protected void setMethodInvocation() {
        if (this instanceof ETMethodInvocationNode) {
            this.lastMethodInvocation = (ETMethodInvocationNode) this;
        } else if (this instanceof ETMethodReturnNode) {
            if (parent.getLastMethodInvocation().getParent() != null)
                this.lastMethodInvocation = parent.getLastMethodInvocation()
                        .getParent().getLastMethodInvocation();

        } else if (parent != null) {
            this.lastMethodInvocation = parent.getLastMethodInvocation();
        }
    }

    /**
     * Adds the child.
     * 
     * @param n the n
     */
    public void addChild(ETNode n) {
        children.add(n);
    }

    /**
     * Sets the children.
     * 
     * @param n the new children
     */
    public void setChildren(LinkedList<ETNode> n) {
        this.children = n;
    }

    /**
     * Gets the children.
     * 
     * @return the children
     */
    public ETNode[] getChildren() {
        return (ETNode[]) children.toArray(new ETNode[children.size()]);
    }

    /**
     * Gets the children list.
     * 
     * @return the children list
     */
    public LinkedList<ETNode> getChildrenList() {
        return children;
    }

    /**
     * Gets the iT nodes array.
     * 
     * @return the iT nodes array
     */
    public ITNode[] getITNodesArray() {
        return (ITNode[]) itNodes.toArray(new ITNode[itNodes.size()]);
    }

    /**
     * Gets the bC.
     * 
     * @return the bC
     */
    public ListOfTerm getBC() {
        if (!VisualDebugger.showImpliciteAttr && bc != null)
            return VisualDebugger.getVisualDebugger().removeImplicite(bc);
        return bc;
    }

    /**
     * Append bc.
     * 
     * @param l the l
     */
    public void appendBC(ListOfTerm l) {
        if (bc != null) // TODO ??????? remove this!
            this.bc = bc.append(l);
        else
            bc = SLListOfTerm.EMPTY_LIST.append(l);
    }

    /**
     * itnode.
     * 
     * @param n the n
     */
    public void addITNode(ITNode n) {
        itNodes.add(n);
    }

    /**
     * it nodes.
     * 
     * @param nodes the nodes
     */
    public void addITNodes(LinkedList<ITNode> nodes) {
        this.itNodes.addAll(nodes);
    }

    /**
     * itnodes.
     * 
     * @return a LinkedList with the ITNodes associated to this ETNodes
     */
    public LinkedList<ITNode> getITNodes() {
        return itNodes;
    }

    /**
     * creates a shallow copy of this node and attaches it to node <tt>p</tt>
     * FIXME: FIX this method as it creates not well linked trees Problems: 1)
     * the children of this node are not linked to their new parent -->
     * malformed tree 2) the children are not copied themselves and linking
     * would destroy the old tree.
     * 
     * @param p the p
     * 
     * @return the ET node
     */
    public ETNode copy(ETNode p) {        
        final ETNode copy = 
            new ETNode(bc, (LinkedList<ITNode>) itNodes.clone(), p);
        copy.setChildren((LinkedList) children.clone());
        return copy;
    }

    /**
     * Compute simplified bc.
     */
    public void computeSimplifiedBC() {
        if (this.bc != null)
            this.simplifiedBC = 
                VisualDebugger.getVisualDebugger().simplify(
                    this.bc);
        else
            simplifiedBC = null;
    }

    /**
     * Gets the simplified bc.
     * 
     * @return the simplified bc
     */
    public ListOfTerm getSimplifiedBc() {
        if (this.simplifiedBC == null)
            return bc;
        else
            return this.simplifiedBC;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return print();
    }

    /**
     * Prints the.
     * 
     * @return the string
     */
    public String print() {
        String result = "";// = "Node\n";
        if (getITNodesArray().length > 0)
            result = result + " ETNode " + getITNodesArray()[0].getId() + "  "
                    + bc;
        else
            result = result + " ETNode " + "  " + bc;
        if (this.lastMethodInvocation != null)
            result += "lmi " + this.lastMethodInvocation.getMethodReference();
        return result;
    }

    /**
     * Checks if is nobc.
     * 
     * @return true, if is nobc
     */
    public boolean isNobc() {
        return nobc;
    }

    /**
     * Sets the nobc.
     * 
     * @param nobc the new nobc
     */
    public void setNobc(boolean nobc) {
        this.nobc = nobc;
    }

    /**
     * Gets the last expression start.
     * 
     * @return the last expression start
     */
    public ETStatementNode getLastExpressionStart() {
        return lastExpressionStart;
    }

    /**
     * Gets the last method invocation.
     * 
     * @return the last method invocation
     */
    public ETMethodInvocationNode getLastMethodInvocation() {
        return lastMethodInvocation;
    }

    /**
     * Gets the parent.
     * 
     * @return the parent
     */
    public ETNode getParent() {
        return parent;
    }

    /**
     * Gets the proof tree nodes.
     * 
     * @return the proof tree nodes
     */
    public ListOfNode getProofTreeNodes() {
        ListOfNode result = SLListOfNode.EMPTY_LIST;
        for (Iterator<ITNode> it = itNodes.iterator(); it.hasNext();) {
            result = result.append(((ITNode) it.next()).getNode());

        }
        return result;
    }

    /**
     * Represents proof tree node.
     * 
     * @param n the n
     * 
     * @return true, if successful
     */
    public boolean representsProofTreeNode(Node n) {
        for (Iterator<ITNode> it = itNodes.iterator(); it.hasNext();) {
            if (((ITNode) it.next()).getNode().equals(n))
                return true;

        }
        return false;

    }

    /**
     * Removes the redundand it nodes.
     */
    public void removeRedundandITNodes() {
        ITNode[] nodes = getITNodesArray();
        boolean[] a = new boolean[nodes.length];
        for (int i = 0; i < a.length; i++) {
            a[i] = false;
        }

        int resultLenght = nodes.length;

        for (int i = 0; i < nodes.length; i++) {
            for (int j = 0; j < nodes.length; j++) {
                if (i != j && !a[j] && !a[i]) {
                    // System.out.println("Redundant? "+nodes[i].getPc()+" ->
                    // "+nodes[j].getPc());
                    if (redundant(nodes[i], nodes[j])) {
                        resultLenght--;
                        a[j] = true;
                    }
                }

            }

        }

        ITNode[] result = new ITNode[resultLenght];
        int resulti = 0;
        for (int i = 0; i < nodes.length; i++) {
            if (!a[i]) {
                result[resulti] = nodes[i];
                resulti++;
            }

        }

    }

    /**
     * Redundant.
     * 
     * @param n1 the n1
     * @param n2 the n2
     * 
     * @return true, if successful
     */
    private boolean redundant(ITNode n1, ITNode n2) {
        DebuggerPO po = new DebuggerPO("DebuggerPO: redundant pc");

        po.setPCImpl(n1.getPc(), n2.getPc());

        po.setIndices(mediator.getProof().env().getInitConfig()
                .createTacletIndex(), mediator.getProof().env().getInitConfig()
                .createBuiltInRuleIndex());
        
        po.setProofSettings(mediator.getProof().getSettings());

        po.setConfig(mediator.getProof().env().getInitConfig());        
        
        final ProofStarter ps = new ProofStarter();
        ps.init(po);
        ps.setUseDecisionProcedure(false);
        ps.getProof().setActiveStrategy(
                (DebuggerStrategy.Factory.create(ps.getProof(),
                        "DebuggerStrategy", new StrategyProperties())));
        ps.run(mediator.getProof().env());
        return ps.getProof().closed();
    }

    /**
     * Checks if is collapsed.
     * 
     * @return true, if is collapsed
     */
    public boolean isCollapsed() {
        return isCollapsed;
    }

    /**
     * Sets the collapsed.
     * 
     * @param isCollapsed the new collapsed
     */
    public void setCollapsed(boolean isCollapsed) {
        this.isCollapsed = isCollapsed;
    }

    /**
     * Checks if is watchpoint.
     * 
     * @return true, if is watchpoint
     */
    public boolean isWatchpoint() {
        return isWatchpoint;
    }

    /**
     * Marks the node as a watchpoint.
     * Set to true if at least one watchpoint is satisfied at this node.
     * @param isWatchpoint the new watchpoint
     */
    public void setWatchpoint(boolean isWatchpoint) {
        this.isWatchpoint = isWatchpoint;
    }

    /**
     * Gets the watchpoints satisfied.
     * 
     * @return the watchpoints satisfied
     */
    public List<WatchPoint> getWatchpointsSatisfied() {
        return watchpointsSatisfied;
    }

    /**
     * Sets the watchpoints satisfied.
     * 
     * @param watchpointsSatisfied the new watchpoints satisfied
     */
    public void setWatchpointsSatisfied(List<WatchPoint> watchpointsSatisfied) {
        this.watchpointsSatisfied = watchpointsSatisfied;
    }

    /**
     * Gets the watchpoints true in subset.
     * 
     * @return the watchpoints true in subset
     */
    public Set<WatchPoint> getWatchpointsTrueInSubset() {
        return watchpointsTrueInSubset;
    }

    /**
     * Adds the watchpoint true in subset.
     * 
     * @param watchpoint the watchpoint
     */
    public void addWatchpointTrueInSubset(WatchPoint watchpoint) {
        watchpointsTrueInSubset.add(watchpoint);
    }
}
