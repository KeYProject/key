package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.Iterator;
import java.util.LinkedList;

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
    private LinkedList children = new LinkedList();

    private ETMethodInvocationNode lastMethodInvocation = null;

    private ETStatementNode lastExpressionStart = null;

    private ETNode parent = null;

    private KeYMediator mediator = VisualDebugger.getVisualDebugger()
            .getMediator();

    private ListOfTerm bc = SLListOfTerm.EMPTY_LIST;

    // ListOfTerm pc= SLListOfTerm.EMPTY_LIST;
    private LinkedList itNodes = new LinkedList();

    private boolean nobc = false;

    private ListOfTerm simplifiedBC = null;

    public ETNode(ListOfTerm bc, ETNode parent) {
        this.bc = bc;
        this.parent = parent;
        this.setMethodInvocation();
    }

    public ETNode(ListOfTerm bc, LinkedList itNodes, ETNode parent) {
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

    public void setChildren(LinkedList n) {
        this.children = n;
    }

    public ETNode[] getChildren() {
        return (ETNode[]) children.toArray(new ETNode[children.size()]);
    }

    public LinkedList getChildrenList() {
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
    public void addITNodes(LinkedList nodes) {
        this.itNodes.addAll(nodes);
    }

    /**
     * itnodes
     * 
     * @return
     */
    public LinkedList getITNodes() {
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
        ETNode copy = new ETNode(bc, (LinkedList) itNodes.clone(), p);
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
        for (Iterator it = itNodes.iterator(); it.hasNext();) {
            result = result.append(((ITNode) it.next()).getNode());

        }
        return result;
    }

    public boolean representsProofTreeNode(Node n) {
        for (Iterator it = itNodes.iterator(); it.hasNext();) {
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
}
