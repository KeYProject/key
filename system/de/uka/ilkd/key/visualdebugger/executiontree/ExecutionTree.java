package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.WatchpointUtil;
import de.uka.ilkd.key.visualdebugger.*;

public class ExecutionTree implements AutoModeListener {

    private static ETNode etNodeRoot = null;
    private static ETNode etTreeBeforeMerge;
    private static boolean hideInf = true;
    private static ITNode itNodeRoot = null;
    public static final int RAWTREE = 1;
    public static final int SLET = 2;
    public static final int SLET2 = 3;
    public static final int SLET3 = 4;
    public static int treeStyle = SLET3;

    public static ETNode getETNode() {
        return etNodeRoot;

    }

    public static ETNode getEtTreeBeforeMerge() {
        return etTreeBeforeMerge;
    }

    public static ITNode getITNode() {
        return itNodeRoot;
    }

    private boolean intro_post;

    private LinkedList listeners = new LinkedList();

    private KeYMediator mediator;

    private VisualDebugger vd = VisualDebugger.getVisualDebugger();

    public ExecutionTree(Proof p, KeYMediator m, boolean b) {
        this.mediator = m;
        intro_post = b;
    }

    public void addListener(DebuggerListener listener) {
        listeners.add(listener);
    }

    // duplicate in updatelabel listener

    public void autoModeStarted(ProofEvent e) {
        vd
                .fireDebuggerEvent(new DebuggerEvent(
                        DebuggerEvent.EXEC_STARTED, null));
    }

    public void autoModeStopped(ProofEvent e) {
        if (intro_post) {
            intro_post();
            intro_post = false;
            vd.setInitPhase(false);
            vd.getBpManager().setNoEx(false);
            vd.stepToFirstSep();
        } else {
            vd.fireDebuggerEvent(new DebuggerEvent(DebuggerEvent.EXEC_FINISHED,
                    null));
        }
        
        final Runnable execTreeThread = new Runnable() {
            public void run() {
                // new StateVisualization(node,mediator);
                createExecutionTree();
            }
        };
        // mediator.invokeAndWait(interfaceSignaller);

        if (mediator.getProof() != null) {
            startThread(execTreeThread);
        }
    }

    public void buildETree(ITNode n, ListOfTerm terms, ETNode parent, String exc) {
        ETNode branch = parent;
        String newExc = exc;
        ListOfTerm bc = terms;
        if (n.getBc() != null) {
            bc = bc.append(n.getBc());
        } else {
            bc = null;
        }

        if (n.getStatementId() != null) {
            branch = new ETStatementNode(bc, n.getStatementId(), parent);
            branch.addITNode(n);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;
            newExc = null;
        } else if (n.getExprId() != null && n.getExprId().isBoolean()) {
            branch = new ETStatementNode(bc, n.getExprId(), parent);
            branch.addITNode(n);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;
            newExc = null;
        } else if (n.isMethodInvocationForET()) {
            branch = new ETMethodInvocationNode(bc, n.getProgramMethod(), n
                    .getMethodReference(), n.getParameter(), n.getValues(),
                    parent);
            branch.addITNode(n);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;
            newExc = null;
        } else if (n.isMethodReturn()
                && n.getParent().getMethodNode().isMethodInvocationForET()) {
            branch = new ETMethodReturnNode(bc, n.getMethodReturnResult(),
                    parent);
            branch.addITNode(n);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;
            newExc = null;
        } else if (n.getChildren().length > 1
                || (n.getChildren().length == 1 && n.getChildren()[0].getBc() == null)) {// this
            // case
            // should
            // not
            // happen
            branch = new ETNode(bc, parent);
            branch.addITNode(n);
            if (n.isNobc())
                branch.setNobc(true);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;

        } else if (n.getChildren().length == 0) {
            branch = createLeafNode(n, bc, exc, parent);
            parent.addChild(branch);
            bc = SLListOfTerm.EMPTY_LIST;
        }

        if (bc == null) {
            bc = SLListOfTerm.EMPTY_LIST;
        }

        if (n.getActStatement() instanceof Throw) {
            newExc = n.getActStatement().toString();
        }

        ITNode[] childs = n.getChildren();
        for (int i = 0; i < childs.length; i++) {
            buildETree(childs[i], bc, branch, newExc);
        }

    }

    private void buildITTree(Node n, int currentId, boolean lookingForBC,
            ITNode parent, ListOfTerm terms) {
        int newId = currentId;
        boolean looking = lookingForBC;
        ITNode newParent = parent;
        ListOfTerm newTerms = terms;

        int gId = greatestLabel(n.getNodeInfo().getVisualDebuggerState()
                .getLabels().values());
        if (gId > currentId) {
            newId = gId;
            looking = true;
        }

        ListOfTerm l = SLListOfTerm.EMPTY_LIST;

        boolean atomic = true;
        if (looking) {
            HashMapFromPosInOccurrenceToLabel labels = n.getNodeInfo()
                    .getVisualDebuggerState().getLabels();
            IteratorOfPosInOccurrence pioIt = labels.keyIterator();

            // case: {u}post TODO
            while (pioIt.hasNext()) {
                PosInOccurrence pio = pioIt.next();
                PCLabel pcLabel = ((PCLabel) labels.get(pio));
                // if (!containsJavaBlock(pio.constrainedFormula().formula()))
                // pc = pc.append(pio.constrainedFormula().formula());

                if (pcLabel.getId() == newId) {

                    if (!isLiteral(pio)) {
                        atomic = false;
                        break;
                    }

                    if (!containsJavaBlock(pio.constrainedFormula().formula())) {
                        Term t = pio.constrainedFormula().formula();
                        if (pio.isInAntec())
                            l = l.append(t);
                        else {
                            if (t.op() == Op.NOT) {
                                l = l.append(t.sub(0));
                            } else
                                l = l
                                        .append(TermFactory.DEFAULT
                                                .createJunctorTermAndSimplify(
                                                        Op.NOT, t));
                        }
                    }
                }
            }

            if (atomic
                    && (!onlyBCInvolvedInTacletApp(n, newId)
                            || n.childrenCount() > 1 || n.childrenCount() == 0)) {
                newTerms = l;
                looking = false;
            }
        }

        if (n.getAppliedRuleApp() != null
                && n.getAppliedRuleApp().posInOccurrence() != null
                && modalityTopLevel(n.getAppliedRuleApp().posInOccurrence())) {
            newParent = new ITNode(newTerms, getPc(n.getNodeInfo()
                    .getVisualDebuggerState().getLabels()), n, parent);
            parent.addChild(newParent);
            newTerms = null;
        } else if (!looking && n.childrenCount() > 1) {
            newParent = new ITNode(newTerms, getPc(n.getNodeInfo()
                    .getVisualDebuggerState().getLabels()), n, parent);
            newParent.setNobc(true);
            parent.addChild(newParent);
            newTerms = null;
        } else if (n.childrenCount() == 0 && !looking) {
            newParent = new ITNode(newTerms, getPc(n.getNodeInfo()
                    .getVisualDebuggerState().getLabels()), n, parent);
            parent.addChild(newParent);
            newTerms = null;
        }

        final IteratorOfNode it = n.childrenIterator();
        while (it.hasNext()) {
            buildITTree(it.next(), newId, looking, newParent, newTerms);
        }
    }

    public void buildSLETWithoutExpr(ETNode n, ETNode parent, ListOfTerm bc) {
        ETNode branch = parent;

        ListOfTerm newBC = bc;

        if (!(n instanceof ETStatementNode) && !(n instanceof ETLeafNode)
                && !(n instanceof ETMethodInvocationNode)
                && !(n instanceof ETMethodReturnNode)) {
            if (n.getBC() != null)
                newBC = newBC.append(n.getBC());

        } else {
            branch = n.copy(parent);
            branch.setChildren(new LinkedList());
            if (n.getBC() != null)
                branch.appendBC(bc);
            parent.addChild(branch);
            newBC = SLListOfTerm.EMPTY_LIST;
        }

        ETNode[] childs = n.getChildren();
        for (int i = 0; i < childs.length; i++) {
            buildSLETWithoutExpr(childs[i], branch, newBC);
        }

    }

    private boolean containsJavaBlock(Term t) {
        if (!t.javaBlock().isEmpty()
                || t.op() == vd.getPostPredicate()) {
            return true; // TODO
        }
        for (int i = 0, ar = t.arity(); i < ar; i++) {
            if (containsJavaBlock(t.sub(i))) {
                return true;
            }
        }
        return false;
    }

    private void createExecutionTree() {
        if (mediator.getProof() == null) {
            itNodeRoot = null;
            etNodeRoot = null;
            return;
        }
        ITNode root = new ITNode(mediator.getProof().root());
        buildITTree(mediator.getProof().root(), -1, false, root,
                SLListOfTerm.EMPTY_LIST);
        ETNode etrr = new ETNode(SLListOfTerm.EMPTY_LIST, null);
        itNodeRoot = root;

        buildETree(root, SLListOfTerm.EMPTY_LIST, etrr, null);
        etTreeBeforeMerge = etrr;
        ETNode merged = mergeTree(etrr, null);
        if (hideInf)
            merged = this.hideInf(merged, null);

        ETNode etrr2 = new ETNode(SLListOfTerm.EMPTY_LIST, null);
        buildSLETWithoutExpr(merged, etrr2, SLListOfTerm.EMPTY_LIST);// mergeTree(etrr);

        etNodeRoot = etrr2.getChildren()[0];
        simplifyBC(etNodeRoot);

        // identify watchpoints
        LinkedList<ETNode> allLeafETNodes = WatchpointUtil.getAllLeafETNodes(etNodeRoot);
        ListOfTerm watchpoints = vd.getWatchPointManager()
        .getListOfWatchpoints(vd.getMediator().getServices());
        
        if (!watchpoints.isEmpty()) {
            WatchpointUtil.setActiveWatchpoint(allLeafETNodes, watchpoints);
        }
 
        fireTreeChanged(root);
    }

    private ETNode createLeafNode(ITNode n, ListOfTerm bc, String exc,
            ETNode parent) {
        ETNode branch;
        if (n.getNode().isClosed()) {
            // System.out.println("new INf");
            branch = new ETLeafNode(bc, ETLeafNode.INFEASIBLE, parent);
            branch.addITNode(n);
        } else {

            SourceElementId progC = vd.getProgramCounter(n.getNode());
            // System.out.println("ProgramC: "+progC);
            if (progC != null) {
                branch = new ETStatementNode(bc, progC, parent);
                branch.addITNode(n);
                // ((ETLeafNode)branch).setProgramCounter(progC);
            } else {

                branch = new ETLeafNode(bc, ETLeafNode.TERMINATED, parent);
                branch.addITNode(n);
                ((ETLeafNode) branch).setExceptionName(exc);
            }
        }

        return branch;
    }

    public boolean exceptionThrown(Node n) {
        final Sequent s = n.sequent();
        for (IteratorOfConstrainedFormula it = s.succedent().iterator(); it
                .hasNext();) {
            ConstrainedFormula cfm = it.next();
            if (vd.modalityTopLevel(new PosInOccurrence(cfm,
                    PosInTerm.TOP_LEVEL, false)) != null)
                return false;

        }
        return true;
    }

    public boolean executionTerminatedNormal(Node n) {
        final Sequent s = n.sequent();
        for (IteratorOfConstrainedFormula it = s.succedent().iterator(); it
                .hasNext();) {
            ConstrainedFormula cfm = it.next();
            final Term f = cfm.formula();
            if (f.op() instanceof QuanUpdateOperator) {
                final Term subOp = ((QuanUpdateOperator) f.op()).target(f);
                if (subOp.op() == vd.getPostPredicate()
                        && subOp.javaBlock().isEmpty()) {
                    return true;
                }
            }
        }
        return false;
    }

    private void fireTreeChanged(ITNode root) {
        synchronized (listeners) {
            DebuggerEvent event = new DebuggerEvent(DebuggerEvent.TREE_CHANGED,
                    root);
            vd.fireDebuggerEvent(event);
        }
    }

    private ListOfTerm getPc(HashMapFromPosInOccurrenceToLabel labels) {
        IteratorOfPosInOccurrence pioIt = labels.keyIterator();
        ListOfTerm pc = SLListOfTerm.EMPTY_LIST;

        while (pioIt.hasNext()) {
            PosInOccurrence pio = pioIt.next();
            // PCLabel pcLabel = ((PCLabel)labels.get(pio));
            if (!containsJavaBlock(pio.constrainedFormula().formula())) {
                Term t = pio.constrainedFormula().formula();
                if (pio.isInAntec())
                    pc = pc.append(t);
                else {
                    if (t.op() == Op.NOT) {
                        pc = pc.append(t.sub(0));
                    } else
                        pc = pc.append(TermFactory.DEFAULT
                                .createJunctorTermAndSimplify(Op.NOT, t));
                }

                // pc = pc.append(pio.constrainedFormula().formula());
            }

        }
        return pc;
    }

    private int greatestLabel(IteratorOfLabel it) {
        int current = -1;
        if (it != null)
            while (it.hasNext()) {
                PCLabel pc = (PCLabel) it.next();
                if (pc.getId() > current)
                    current = pc.getId();
            }
        return current;
    }

    public ETNode hideInf(ETNode n, ETNode parent) {
        ETNode newNode = n.copy(parent);
        ETNode[] childs = n.getChildren();
        LinkedList newChilds = new LinkedList();

        for (int i = 0; i < childs.length; i++) {
            ETNode child = childs[i];
            if (child instanceof ETLeafNode
                    && ((ETLeafNode) child).getState() == ETLeafNode.INFEASIBLE) {
                // System.out.println("asfasfasgag");

            } else {
                newChilds.add(hideInf(child, newNode));
            }
        }
        newNode.setChildren(newChilds);
        return newNode;

    }

    private void intro_post() {
        ListOfGoal goals = mediator.getProof().getSubtreeGoals(
                mediator.getProof().root());

        IteratorOfGoal it = goals.iterator();
        while (it.hasNext()) {
            Goal g = it.next();
            Semisequent s = g.node().sequent().succedent();
            IteratorOfConstrainedFormula cfmIt = s.iterator();

            while (cfmIt.hasNext()) {
                ConstrainedFormula cfm = (ConstrainedFormula) cfmIt.next();

                PosInOccurrence pio = new PosInOccurrence(cfm,
                        PosInTerm.TOP_LEVEL, false);

                SetOfTacletApp set = mediator.getTacletApplications(g,
                        "introduce_post_predicate", pio);

                // SetOfTacletApp set = m.getTacletApplications(g,
                // "cut", pio);

                if (set.size() > 0) {
                    TacletApp tapp = set.iterator().next();
                    g.node().getNodeInfo().getVisualDebuggerState().getLabels()
                            .put(pio, new PCLabel(g.node().serialNr(), false));
                    vd.extractInput(g.node(), pio);
                    vd.extractPrecondition(g.node(), pio);

                    // VisualDebugger.getVisualDebugger().bpManager.clearSteps();
                    mediator.getInteractiveProver().applyInteractive(tapp, g);

                }

            }
        }
    }

    private boolean isInfeasibleLeaf(ETNode n) {
        return (n instanceof ETLeafNode && ((ETLeafNode) n).getState() == ETLeafNode.INFEASIBLE);

    }

    private boolean isLiteral(PosInOccurrence pio) {
        Term f = pio.constrainedFormula().formula();
        Operator op = f.op();

        if (this.modalityTopLevel(pio)) {
            return true;
        }
        if (op == Op.AND
                || op == Op.OR
                || op == Op.IF_THEN_ELSE
                || op == Op.IF_EX_THEN_ELSE
                || op == Op.EQV
                || op == Op.IMP
                || op == Op.AND
                || (op instanceof IUpdateOperator
                /* && !containsJavaBlock(pio.constrainedFormula().formula() */)) {
            return false;
        }
        final OpCollector col = new OpCollector();
        f.execPostOrder(col);

        return !(col.contains(Op.IF_EX_THEN_ELSE) || col
                .contains(Op.IF_THEN_ELSE));
    }

    private boolean isNoInfeasibleLeaf(ETNode n) {
        return (n instanceof ETLeafNode && ((ETLeafNode) n).getState() != ETLeafNode.INFEASIBLE);
    }

    private ETNode mergeNodes(ETNode n1, ETNode n2, ETNode parent) {
        // VisualDebugger.print("mergeNodes "+n1.print()+" "+n2.print());

        if (this.isInfeasibleLeaf(n1)) { // TODO wrong?
            return n2.copy(parent);
        } else if (this.isInfeasibleLeaf(n2)) {
            return n1.copy(parent);
        } else if (this.isInfeasibleLeaf(n2)) {
            return n1.copy(parent);
        }
        if (this.isNoInfeasibleLeaf(n1)) { // TODO wrong?
            final ETNode n = n2.copy(parent);
            n.addITNodes(n1.getITNodes());
            return n1;
        } else if (this.isNoInfeasibleLeaf(n2)) {
            final ETNode n = n1.copy(parent);
            n.addITNodes(n2.getITNodes());
            return n2;
        }
        if (n1.getChildren().length == 0) { // TODO wrong?
            final ETNode n = n2.copy(parent);
            n.addITNodes(n1.getITNodes());
            return n;
        } else if (n2.getChildren().length == 0) {
            final ETNode n = n1.copy(parent);
            n.addITNodes(n2.getITNodes());
            return n;
        }

        ETNode n = n1.copy(parent);
        n.addITNodes(n2.getITNodes());

        n.setChildren(new LinkedList());

        if (n1.getChildren().length != n2.getChildren().length) {
            VisualDebugger.print("Merging Nodes: Sth wrong ");
            VisualDebugger.print("Node " + n1.getITNodesArray()[0].getId()
                    + " " + n1.getITNodesArray()[0].getNode().sequent());
            VisualDebugger.print("Node " + n2.getITNodesArray()[0].getId()
                    + " " + n2.getITNodesArray()[0].getNode().sequent());
            VisualDebugger.print("" + n1.getChildren().length);
            VisualDebugger.print("" + n2.getChildren().length);
            throw new RuntimeException(
                    "expected same number of childs in mergetree");
        }

        for (int i = 0; i < n1.getChildren().length; i++) {
            n.addChild(mergeNodes(n1.getChildren()[i], n2.getChildren()[i], n));
        }

        return n;
    }

    public ETNode mergeTree(ETNode n, ETNode parent) {
        VisualDebugger.print("mergeTree " + n.print());

        ETNode newNode = n.copy(parent);
        ETNode[] childs = n.getChildren();

        LinkedList mergedChilds = new LinkedList();

        for (int i = 0; i < childs.length; i++) {
            mergedChilds.add(mergeTree(childs[i], newNode));
        }

        newNode.setChildren(mergedChilds);

        // ETNode[] mergedChildsArray= mergedChilds.toArray();

        if (mergedChilds.size() > 1) {

            ETNode m1 = (ETNode) mergedChilds.getFirst();
            // if (this.maxmerge>0 && this.merged<this.maxmerge)
            if (n.isNobc()) {

                // if (m1.getBc()==null){
                VisualDebugger
                        .print("Merge: " + n.getITNodesArray()[0].getId());
                for (int i = 1; i < mergedChilds.size(); i++) {

                    m1 = mergeNodes(m1, (ETNode) mergedChilds.get(i), parent);

                }
                if (n.getBC() != null)
                    m1.appendBC(n.getBC());

                return m1;

                // if (n.getBc()!=null)
                // m1.getChilds()[0].appendBc(n.getBc()); //TODO ??
                // return m1.getChilds()[0];

            }

        }

        return newNode;
    }

    /**
     * FIXME reuse method in VisualDebugger
     * 
     * @param pio
     * @return
     */
    private boolean modalityTopLevel(PosInOccurrence pio) {
        Term cf = pio.constrainedFormula().formula();
        if (cf.arity() > 0) {
            // CHECK: if --> while?
            if (cf.op() instanceof QuanUpdateOperator) {
                cf = ((QuanUpdateOperator) cf.op()).target(cf);
            }
            if (cf.op() instanceof Modality
                    || cf.op() == vd.getPostPredicate()) {
                return true;
            }
        }
        return false;
    }

    // TODO allow all rules that are not of the form assume(non pc) fing(pc)
    // TODO splitting rules in updates
    private boolean onlyBCInvolvedInTacletApp(Node n, int newId) {
        HashMapFromPosInOccurrenceToLabel labels = n.getNodeInfo()
                .getVisualDebuggerState().getLabels();

        if (n.childrenCount() == 0) {
            // System.out.println("BBBBBBBBB "+n.serialNr());
            return false;

        }

        if (n.getAppliedRuleApp() instanceof TacletApp) {
            TacletApp tapp = (TacletApp) n.getAppliedRuleApp();

            PosInOccurrence pioFocus = tapp.posInOccurrence().topLevel();
            if (modalityTopLevel(pioFocus))
                return false;

            if (!labels.containsKey(pioFocus)
                    || ((PCLabel) labels.get(pioFocus)).getId() != newId)
                return false;

            if (tapp.ifFormulaInstantiations() != null)
                for (IteratorOfIfFormulaInstantiation it = tapp
                        .ifFormulaInstantiations().iterator(); it.hasNext();) {
                    final IfFormulaInstantiation next = it.next();
                    if (next instanceof IfFormulaInstSeq) {
                        IfFormulaInstSeq i = (IfFormulaInstSeq) next;
                        PosInOccurrence pio = new PosInOccurrence(i
                                .getConstrainedFormula(), PosInTerm.TOP_LEVEL,
                                i.inAntec());
                        if (!labels.containsKey(pio)
                                || ((PCLabel) labels.get(pio)).getId() != newId) {
                            return false;
                        }
                    }
                }

        }

        return true;
    }

    public void setListeners(LinkedList l) {
        this.listeners = l;
    }

    private void simplifyBC(ETNode n) {
        ETNode[] children = n.getChildren();
        if (children.length > 1)
            for (int i = 0; i < children.length; i++) {
                children[i].computeSimplifiedBC();
            }

        n.removeRedundandITNodes();

        for (int i = 0; i < children.length; i++) {
            simplifyBC(children[i]);
        }
    }

    private void startThread(final Runnable r) {
        mediator.stopInterface(false);
        Thread appThread = new Thread() {
            public void run() {
                try {
                    SwingUtilities.invokeAndWait(r);
                    // worker.start();
                } catch (Exception e) {
                    e.printStackTrace();
                }
                mediator.startInterface(false);
                mediator.setInteractive(true);
                VisualDebugger.print("Finished creation of ET "
                        + Thread.currentThread());
            }
        };
        appThread.start();
    }
}
