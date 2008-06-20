// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

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
    
    private LinkedList<ETNode> children = new LinkedList<ETNode>();

    private ETMethodInvocationNode lastMethodInvocation = null;

    private ETStatementNode lastExpressionStart = null;

    private ETNode parent = null;

    private KeYMediator mediator = VisualDebugger.getVisualDebugger()
            .getMediator();

    private ListOfTerm bc = SLListOfTerm.EMPTY_LIST;
    private List<WatchPoint> watchpointsSatisfied = null;

    // ListOfTerm pc= SLListOfTerm.EMPTY_LIST;
    private LinkedList<ITNode> itNodes = new LinkedList<ITNode>();

    private boolean nobc = false;
    private boolean isCollapsed = false;
    private boolean isWatchpoint = false;
    
    private ListOfTerm simplifiedBC = null;

    public ETNode(ListOfTerm bc, ETNode parent) {
        this.bc = bc;
        this.parent = parent;
        this.setMethodInvocation();
    }

    public ETNode(ListOfTerm bc, LinkedList<ITNode> itNodes, ETNode parent) {
        this.bc = bc;
        this.itNodes = itNodes;
        this.parent = parent;
        this.setMethodInvocation();
    }

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

    public void addChild(ETNode n) {
        children.add(n);
    }

    public void setChildren(LinkedList<ETNode> n) {
        this.children = n;
    }

    public ETNode[] getChildren() {
        return (ETNode[]) children.toArray(new ETNode[children.size()]);
    }

    public LinkedList<ETNode> getChildrenList() {
        return children;
    }

    public ITNode[] getITNodesArray() {
        return (ITNode[]) itNodes.toArray(new ITNode[itNodes.size()]);
    }

    public ListOfTerm getBC() {
        if (!VisualDebugger.showImpliciteAttr && bc != null)
            return VisualDebugger.getVisualDebugger().removeImplicite(bc);
        return bc;
    }

    public void appendBC(ListOfTerm l) {
        if (bc != null) // TODO ??????? remove this!
            this.bc = bc.append(l);
        else
            bc = SLListOfTerm.EMPTY_LIST.append(l);
    }

    /**
     * itnode
     * 
     * @param n
     */
    public void addITNode(ITNode n) {
        itNodes.add(n);
    }

    /**
     * it nodes
     * 
     * @param nodes
     */
    public void addITNodes(LinkedList<ITNode> nodes) {
        this.itNodes.addAll(nodes);
    }

    /**
     * itnodes
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
     * would destroy the old tree
     * 
     */
    public ETNode copy(ETNode p) {        
        final ETNode copy = 
            new ETNode(bc, (LinkedList<ITNode>) itNodes.clone(), p);
        copy.setChildren((LinkedList) children.clone());
        return copy;
    }

    public void computeSimplifiedBC() {
        if (this.bc != null)
            this.simplifiedBC = 
                VisualDebugger.getVisualDebugger().simplify(
                    this.bc);
        else
            simplifiedBC = null;
    }

    public ListOfTerm getSimplifiedBc() {
        if (this.simplifiedBC == null)
            return bc;
        else
            return this.simplifiedBC;
    }

    public String toString() {
        return print();
    }

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

    public boolean isNobc() {
        return nobc;
    }

    public void setNobc(boolean nobc) {
        this.nobc = nobc;
    }

    public ETStatementNode getLastExpressionStart() {
        return lastExpressionStart;
    }

    public ETMethodInvocationNode getLastMethodInvocation() {
        return lastMethodInvocation;
    }

    public ETNode getParent() {
        return parent;
    }

    public ListOfNode getProofTreeNodes() {
        ListOfNode result = SLListOfNode.EMPTY_LIST;
        for (Iterator<ITNode> it = itNodes.iterator(); it.hasNext();) {
            result = result.append(((ITNode) it.next()).getNode());

        }
        return result;
    }

    public boolean representsProofTreeNode(Node n) {
        for (Iterator<ITNode> it = itNodes.iterator(); it.hasNext();) {
            if (((ITNode) it.next()).getNode().equals(n))
                return true;

        }
        return false;

    }

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

    public boolean isCollapsed() {
        return isCollapsed;
    }

    public void setCollapsed(boolean isCollapsed) {
        this.isCollapsed = isCollapsed;
    }

    public boolean isWatchpoint() {
        return isWatchpoint;
    }

    public void setWatchpoint(boolean isWatchpoint) {
        this.isWatchpoint = isWatchpoint;
    }

    public List<WatchPoint> getWatchpointsSatisfied() {
        return watchpointsSatisfied;
    }

    public void setWatchpointsSatisfied(List<WatchPoint> watchpointsSatisfied) {
        this.watchpointsSatisfied = watchpointsSatisfied;
    }
}
