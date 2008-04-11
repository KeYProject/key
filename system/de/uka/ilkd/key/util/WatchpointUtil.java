package de.uka.ilkd.key.util;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.Map.Entry;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.ListOfRuleSet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.*;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class WatchointUtil.
 * 
 * This Class offers some tools to identify and mark Watchpoints in the current
 * program state, respectivly in the ExecutionTree ET.
 * 
 */
public class WatchpointUtil {

    /**
     * satisfiesWatchpoint returns true, if all leaf nodes in this ETNode
     * satisfy at least one watchpoint from the list
     */
    private static boolean satisfiesWatchpoint(HashSet<Node> leafNodesInETNode,
            List<WatchPoint> watchpoints, ETNode etn) {

        assert leafNodesInETNode != null;
        assert leafNodesInETNode.size() != 0 : "No node to process /in satisfiesWatchpoint /in WatchpointUtil";
        assert watchpoints != null;
        assert watchpoints.size() != 0 : "No watchpoint to evaluate /in satisfiesWatchpoint /in WatchpointUtil";

        LinkedList<Term> watches = new LinkedList<Term>();
        LinkedList<Term> intersection = new LinkedList<Term>();
        for (WatchPoint watchPoint : watchpoints) {
            watches.add(watchPoint.getWatchpointAsTerm());
        }
        intersection = watches;
        System.out.println("watches computed for " + leafNodesInETNode.size()
                + " leafnodes..");
        for (Node node : leafNodesInETNode) {

            List<Term> temp = new LinkedList<Term>();

            PosInOccurrence pos = findPos(node.sequent().succedent());
            if (pos == null)
                pos = findPos(node.sequent().antecedent());

            if (pos != null) {
                for (Term watchpoint : watches) {

                    if (WatchpointUtil.evalutateWatchpoint(node, watchpoint,
                            node.sequent(), pos, node.proof(), 250, watchpoints)) {
                        temp.add(watchpoint);
                        System.out.println("wp evaluated to true");
                    }
                }
            } else {
                System.out.println("POS was NULL!");
            }
            intersection.retainAll(temp);
            System.out
            .println("wps evaluated to true (after intersection) for current node:"
                    + intersection.size());
        }
        etn.setWatchpointsSatisfied(intersection);
        System.out.println("LEAVING satisfiesWP...with "
                + !intersection.isEmpty());
        return !intersection.isEmpty();
    }

    private static PosInOccurrence findPos(Semisequent seq) {

        IteratorOfConstrainedFormula iter = seq.iterator();
        ConstrainedFormula constrainedFormula;
        PosInOccurrence pos = null;
        Term term;
        // iterate over all constrained formulae
        while (iter.hasNext()) {
            constrainedFormula = iter.next();
            pos = new PosInOccurrence(constrainedFormula, PosInTerm.TOP_LEVEL,
                    false);
            term = constrainedFormula.formula();

            // {U1}{U2}...{Un} <prg> phi
            // proceed to update that is directly in front of the modality
            while (term.op() instanceof QuanUpdateOperator) {
                int targetPos = ((QuanUpdateOperator) term.op()).targetPos();
                pos = pos.down(targetPos);
                term = term.sub(targetPos);
            }

            if (term.op() instanceof Modality) {

                SourceElement firstStatement = getFirstActiveStatement(term);
                if (firstStatement.toString().startsWith("Debug")) {
                    System.out.println("LEAVING findPos WITH result...");
                    return pos;
                } else {
                    System.out.println("continue...");
                    continue;
                }
            }
        }

        System.out.println("LEAVING findPos WITHOUT result...");
        return null;
    }

    /**
     */
    private static SourceElement getFirstActiveStatement(Term term) {

        assert term.op() instanceof Modality;
        ProgramPrefix programPrefix = (ProgramPrefix) term.javaBlock()
        .program();

        programPrefix = programPrefix.getPrefixElementAt(programPrefix
                .getPrefixLength() - 1);

        return PosInProgram.getProgramAt(
                programPrefix.getFirstActiveChildPos(), programPrefix)
                .getFirstElement();
    }

    private static HashSet<Node> findLeaves(Node currentNode,
            List<Node> proofnodes) {

        HashSet<Node> result = new HashSet<Node>(3);
        IteratorOfNode iter = currentNode.childrenIterator();
        while (iter.hasNext()) {
            Node child = (Node) iter.next();
            if (proofnodes.contains(child)) {
                proofnodes.remove(child);
                result.addAll(findLeaves(child, proofnodes));
            }
        }
        if (result.isEmpty()) {
            result.add(currentNode);
        }
        return result;
    }

    /**
     * EvaluateWatchpoint.
     * 
     * Evaluates a single watchpoint.
     * 
     * @return true, if the watchpoint is satisfied in the current state
     */
    public static boolean evalutateWatchpoint(Node node, Term watchpoint,
            Sequent seq, PosInOccurrence pos, Proof proof, int maxsteps, List<WatchPoint> watchpoints) {

        UpdateFactory updateFactory = new UpdateFactory(proof.getServices(),
                proof.simplifier());
        LinkedList<Update> updates = new LinkedList<Update>();
        // start tracking names if necessary 
        
        if (WatchPointManager.existsWatchPointContainingLocals()) {

            getInitialRenamings(node, watchpoints);
            checkNamespace(node, watchpoints, updateFactory, updates);
            updates.add(buildNameUpdates(updateFactory, trackRenaming(node, watchpoints), node, watchpoints));
        }

        updates.addAll(collectUpdates(pos));
        for (Update update : updates) {
            watchpoint = updateFactory.prepend(update, watchpoint);
        }
        ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
        seq = seq.changeFormula(newCF, pos).sequent();
        try {
            // start side proof
            final ProofStarter ps = new ProofStarter();
            final ProofEnvironment proofEnvironment = createProofEnvironment(
                    seq, proof, maxsteps, ps);

            if (SwingUtilities.isEventDispatchThread())
                ps.run(proofEnvironment);
            else {
                SwingUtilities.invokeAndWait(new Runnable() {
                    public void run() {
                        ps.run(proofEnvironment);

                    }
                });
            }
            System.out.println("LEAVING evaluateWP...");
            return ps.getProof().closed();
        } catch (Throwable t) {
            System.out.println(t.toString());
            t.printStackTrace();
        }
        return false;
    }

    /**
     * @param node
     * @param watchpoints
     * @param updateFactory
     * @param updates
     */
    private static void checkNamespace(Node node, List<WatchPoint> watchpoints,
            UpdateFactory updateFactory, LinkedList<Update> updates) {
        
        for(WatchPoint wp : watchpoints){
            for(int i = 0;  i < wp.getOrginialLocalVariables().size(); i++){
                LocationVariable orginialLocationVariable = wp.getOrginialLocalVariables().get(i);
                LocationVariable renamedLocationVariable = wp.getInittiallyRenamedLocalVariables().get(i);

                if(node.getGlobalProgVars().contains(renamedLocationVariable ) ){

                    System.out.println("+++ detected relevant variable in namespace");

                    updates.add(updateFactory.elementaryUpdate(
                            TermFactory.DEFAULT.createVariableTerm(orginialLocationVariable),
                            TermFactory.DEFAULT.createVariableTerm(renamedLocationVariable)));
                }
            }
        }
    }

    /**
     * @param pos
     * @return the list of updates found along the given position
     */
    private static LinkedList<Update> collectUpdates(PosInOccurrence pos) {
        LinkedList<Update> updates = new LinkedList<Update>();
        // collect all updates
        PIOPathIterator it = pos.iterator();
        while (it.hasNext()) {
            it.next();
            Term term = it.getSubTerm();
            Operator operator = term.op();
            if (operator instanceof QuanUpdateOperator) {

                Update update = Update.createUpdate(term);
                updates.addFirst(update);
            }
        }
        return updates;
    }

    // TODO
    /**
     * EvaluateWatchpoints.
     * 
     * Returns true, if the concatenation of all watchpoints by the junctor can
     * be evaluated to true, i.e. the proof can be closed
     * 
     * Example: 
     *  watchpoints: w1, w2, w3 
     *      junctor: /\ (AND - logical conjunction) -> evaluates w1 /\ w2 /\ w3 
     *               \/ (OR  - logical disjunction) -> evalutaes w1 \/ w2 \/ w3
     * 
     * @param watchpoints -
     *                a list of all watchpoints that have to be taken into
     *                account
     * @param seq -
     *                the sequent
     * @param pos -
     *                the PosInOcc
     * @param proof -
     *                the proof
     * @param junctor -
     *                the junctor to use
     * @param negateJunctor -
     *                set this to true, if you want to realize NOR/NAND
     *                concatenation
     * @param maxsteps -
     *                the upper bound of steps that should be applied to close
     *                the proof
     */
    public static boolean evalutateWatchpoints(Node node,
            List<WatchPoint> watchpoints, Sequent seq, PosInOccurrence pos,
            Proof proof, Junctor junctor, boolean negateJunctor, int maxsteps) {

        UpdateFactory updateFactory = new UpdateFactory(
                proof.getServices(), proof.simplifier());
        LinkedList<Update> updates = new LinkedList<Update>();

        if (watchpoints.isEmpty()) {
            return false;
        } else {
            if (watchpoints.size() == 1) {

                WatchPoint wp = (WatchPoint) watchpoints
                .toArray()[0];
                return WatchpointUtil.evalutateWatchpoint(node, wp.getWatchpointAsTerm(), seq, pos, proof, maxsteps, watchpoints);
            }
            // start tracking names if necessary
            if (WatchPointManager.existsWatchPointContainingLocals()) {

                getInitialRenamings(node, watchpoints);
                updates.add(buildNameUpdates(updateFactory, trackRenaming(node,
                        watchpoints), node, watchpoints));
            }

            updates.addAll(collectUpdates(pos));

            final TermFactory tf = TermFactory.DEFAULT;
            Iterator<WatchPoint> iter = watchpoints.iterator();

            Term watchpoint = (Op.OR == junctor ? tf.createJunctorTerm(junctor,
                    ((WatchPoint)iter.next()).getWatchpointAsTerm(), tf.createJunctorTerm(Op.FALSE)) : tf
                    .createJunctorTerm(junctor, ((WatchPoint)iter.next()).getWatchpointAsTerm(), tf
                            .createJunctorTerm(Op.TRUE)));

            while (iter.hasNext()) {
                watchpoint = tf.createJunctorTerm(junctor, ((WatchPoint)iter.next()).getWatchpointAsTerm(),
                        watchpoint);
            }
            if (negateJunctor) {
                watchpoint = tf.createJunctorTerm(Op.NOT, watchpoint);
            }
            for (Update update : updates) {
                watchpoint = updateFactory.prepend(update, watchpoint);
            }

            ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
            seq = seq.changeFormula(newCF, pos).sequent();
            // start side proof
            final ProofStarter ps = new ProofStarter();
            final ProofEnvironment proofEnvironment = createProofEnvironment(
                    seq, proof, maxsteps, ps);
            try {
                SwingUtilities.invokeAndWait(new Runnable() {
                    public void run() {
                        ps.run(proofEnvironment);

                    }
                });
            } catch (InterruptedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (InvocationTargetException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            return ps.getProof().closed();
        }
    }

    /**
     * @param seq
     * @param proof
     * @param maxsteps
     * @param ps
     * @return the ProofEnvrionment
     */
    private static ProofEnvironment createProofEnvironment(Sequent seq,
            Proof proof, int maxsteps, final ProofStarter ps) {

        final ProofEnvironment proofEnvironment = proof.env();
        InitConfig initConfig = proofEnvironment.getInitConfig();

        WatchpointPO watchpointPO = new WatchpointPO("WatchpointPO", seq);
        watchpointPO.setIndices(initConfig.createTacletIndex(), initConfig
                .createBuiltInRuleIndex());

        StrategyProperties strategyProperties = DebuggerStrategy
        .getDebuggerStrategyProperties(true, false, false,
                new LinkedList<WatchPoint>());
        final StrategyFactory factory = new DebuggerStrategy.Factory();
        Strategy strategy = (factory.create(proof, strategyProperties));
        watchpointPO.setProofSettings(proof.getSettings());
        watchpointPO.setInitConfig(initConfig);
        ps.setStrategy(strategy);
        ps.setMaxSteps(maxsteps);
        ps.init(watchpointPO);

        return proofEnvironment;
    }

    /**
     * getAllLeaveNodes() returns all ETNodes that are leaves in the current
     * ExecutionTree, which is passed as ETNode as well.
     * 
     * 
     * @return a LinkedList containing all leaves of the current ET
     */
    public static LinkedList<ETNode> getAllLeafETNodes(ETNode etn) {

        LinkedList<ETNode> leaves = new LinkedList<ETNode>();
        LinkedList<ETNode> children = etn.getChildrenList();

        if (children.size() == 0) {
            leaves.add(etn);
            return leaves;
        } else {
            for (ETNode node : children) {
                leaves.addAll(getAllLeafETNodes(node));
            }
        }
        return leaves;
    }

    /**
     * getAllLeafNodes
     * 
     * @param nodes -
     *                an array containing all (proof)nodes of an ETNode
     * @return leaves - a LinkedList with all leaf proofnodes in the ETNode
     */
    public static HashSet<Node> getLeafNodesInETNode(Node[] nodes) {

        assert nodes != null : "The parameter Node[] (proof)nodes was null / in getLeafNodesInETNode()/ in WatchpointUtil!";
        assert nodes.length != 0 : "No nodes contained in the passed Array /in getLeafNodesInETNode() / in WatchpointUtil!";
        // create a collection from the array -> type conversion
        // since getProofTreeNodes() only returns a ListOfNode which
        // does not implement the Collection interface

        // handle simple case
        if (nodes.length == 1) {
            final HashSet<Node> theNode = new HashSet<Node>(1);
            theNode.add(nodes[0]);
            return theNode;
        }
        List<Node> proofnodes = new LinkedList<Node>(Arrays.asList(nodes));
        // not more than 4 children expected
        final int INITIALCAPACITY = 4;
        HashSet<Node> candidates = new HashSet<Node>(INITIALCAPACITY);
        while (!proofnodes.isEmpty()) {

            Node currentNode = proofnodes.get(0);
            proofnodes.remove(currentNode);
            Node parentNode = currentNode.parent();
            while (parentNode != null && proofnodes.contains(parentNode)) {
                proofnodes.remove(parentNode);
                parentNode = parentNode.parent();

            }
            candidates.addAll(findLeaves(currentNode, proofnodes));
        }
        System.out.println("candiates.size: " + candidates.size());
        return candidates;
    }

    /**
     * setActiveWatchpoints
     * 
     * @param nodes -
     *                a list of ETNodes of the current ET. The watchpoints will
     *                be evaluated for all these nodes.
     */
    public static void setActiveWatchpoint(List<ETNode> nodes,
            List<WatchPoint> watchpoints) {
        System.out.println("setting watchpoints active...");
        try {
            for (ETNode node : nodes) {

                HashSet<Node> leafNodesInETNode = getLeafNodesInETNode(node
                        .getProofTreeNodes().toArray());

                node.setWatchpoint(satisfiesWatchpoint(
                        leafNodesInETNode, watchpoints, node));
                System.out.println("LEAVING setActiveWatchpoint...");
            }
        } catch (Throwable t) {
            System.out.println(t.toString());
        }
    }

    /**
     * Gets the executiontree as list.
     * 
     * @param etn
     *                the ETNode containing the current ET
     * 
     * @return the executiontree as list
     */
    public static LinkedList<ETNode> getETasList(ETNode etn) {

        LinkedList<ETNode> executionTree = new LinkedList<ETNode>();
        executionTree.add(etn);
        LinkedList<ETNode> children = etn.getChildrenList();

        for (ETNode node : children) {
            executionTree.addAll(getETasList(node));
        }
        return executionTree;
    }

    public static ListOfRenamingTable trackRenaming(Node node, List<WatchPoint> watchpoints) {

        ListOfRenamingTable allRenamings = SLListOfRenamingTable.EMPTY_LIST;

        // climb the tree
        ListOfNode lon = SLListOfNode.EMPTY_LIST;
        while (node.parent() != null) {
            for (WatchPoint watchPoint : watchpoints) {
                List<LocationVariable> orginialLocalVariables = watchPoint.getOrginialLocalVariables();
                for (LocationVariable locVar : orginialLocalVariables) {
                    Node thatParent = node.parent();
                    Node thatNode = node;
                    try {

                        if(thatNode.getGlobalProgVars().contains(locVar)
                                && !thatParent.getGlobalProgVars().contains(locVar)){

                            System.out.println("node contains local variable" + node.parent().serialNr());
                        }
                    } catch (RuntimeException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                } 
            }

            lon = lon.append(node.parent());
            node = node.parent();

        }

        lon = lon.reverse();
        // walk back on the same branch
        IteratorOfNode it = lon.iterator();
        while (it.hasNext()) {
            Node currentNode = it.next();
            ListOfRenamingTable renamingTables = currentNode.getRenamingTable();
            if (renamingTables != null && renamingTables.size() > 0) {
                System.out.println("found renaming @node: " + currentNode.serialNr());
                IteratorOfRenamingTable i = renamingTables.iterator();

                while (i.hasNext()) {
                    allRenamings = allRenamings.append(i.next());
                }
            }

        }
        return allRenamings;
    }

    /**
     * Gets the initial renamings.
     * 
     * @param node the node
     * 
     * @return the initial renamings
     */
    public static List<LocationVariable> getInitialRenamings(Node node,  List<WatchPoint> watchpoints) {

        Node currentNode = node;
        Node parent = currentNode.parent();
        List<LocationVariable> renamedLocalVariables = new LinkedList<LocationVariable>();
        ProgramMethod programMethod = null;
        int parameterCount = 0;

        while (parent != null) {

            if (parent.getAppliedRuleApp().rule() instanceof Taclet) {

                if (isMethodExpandRule(((Taclet) parent.getAppliedRuleApp()
                        .rule()).getRuleSets())) {

                    // treat parent, i.e. the method-body-statement to get parameter information
                    SourceElement parentElement = getStatement(parent);
                    if (parentElement instanceof StatementBlock) {

                        MethodBodyStatement mbs = (MethodBodyStatement) parentElement
                        .getFirstElement();
                        MethodVisitor mbsVisitor = new MethodVisitor(mbs, node.proof().getServices());
                        mbsVisitor.start();
                        programMethod = mbs.getProgramMethod(node.proof()
                                .getServices());
                        parameterCount = programMethod
                        .getParameterDeclarationCount();

                        LinkedList<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod, watchpoints);

                        for (Integer index : parameterIndices) {
                            renamedLocalVariables.add((LocationVariable) programMethod
                                    .getParameterDeclarationAt(index.intValue()).getVariableSpecification().getProgramVariable());
                        }
                    }
                    // treat currentnode, i.e. the method-frame
                    SourceElement element = getStatement(currentNode);
                    //  Before getting the finally renamed variables we have to get all variables that are declared
                    //  in the method body. The resulting positions are not correct yet since the parameter count is missing.
                    if (element instanceof MethodFrame) {
                        MethodVisitor mv = new MethodVisitor((MethodFrame) element, currentNode.proof().getServices());
                        mv.start();
                        renamedLocalVariables.addAll(addParameterCount(
                                programMethod, valueToKey(mv.result()),
                                parameterCount, watchpoints));
                    }

                    for (WatchPoint wp : watchpoints) {
                        if(wp.getProgramMethod().equals(programMethod)){
                            wp.setInittiallyRenamedLocalVariables(renamedLocalVariables);
                        }
                    }
                }
            }
            currentNode = parent;
            parent = currentNode.parent();
        }
        return renamedLocalVariables;
    }

    /**
     * @param node
     */
    private static SourceElement getStatement(Node node) {
        try {

            IteratorOfConstrainedFormula iterator = node.sequent().iterator();
            ConstrainedFormula constrainedFormula;
            Term term;
            while (iterator.hasNext()) {
                constrainedFormula = iterator.next();
                term = constrainedFormula.formula();

                while (term.op() instanceof QuanUpdateOperator) {
                    int targetPos = ((QuanUpdateOperator) term.op())
                    .targetPos();
                    term = term.sub(targetPos);
                }
                // proceed to most inner method-frame
                if (term.op() instanceof Modality) {
                    ProgramPrefix programPrefix = (ProgramPrefix) term
                    .javaBlock().program();
                    return programPrefix.getPrefixElementAt(programPrefix
                            .getPrefixLength() - 1);

                }
            }
        } catch (RuntimeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

    public static HashMap<Integer, SourceElement> valueToKey(
            Map<SourceElement, Integer> map) {

        HashMap<Integer, SourceElement> newHashMap = new HashMap<Integer, SourceElement>();
        Iterator<Entry<SourceElement, Integer>> it = map.entrySet().iterator();
        while (it.hasNext()) {
            Entry<SourceElement, Integer> entry = (Entry<SourceElement, Integer>) it
            .next();
            newHashMap.put(entry.getValue(), entry.getKey());

        }
        return newHashMap;
    }

    private static boolean isMethodExpandRule(ListOfRuleSet listOfRuleSet) {
        return listOfRuleSet.contains(
                new RuleSet(
                        new Name("method_expand")));
    }

    /**
     * Gets the indices of all parameters that are used in watchpoints for the
     * given method.
     * 
     * @param programMethod
     *                the program method
     * 
     * @return the parameter indices of method, null if no local variables are
     *         used
     */
    private static LinkedList<Integer> getParameterIndicesOfMethod(
            ProgramMethod programMethod, List<WatchPoint> watchpoints) {

        int parameterCount = programMethod.getParameterDeclarationCount();
        LinkedList<Integer> parameterIndices = new LinkedList<Integer>();

        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(programMethod)){
                for (Integer position : watchPoint.getKeyPositions()) {

                    if( position.intValue() < parameterCount) {
                        parameterIndices.add(position);
                    }
                }
            }
        }
        return parameterIndices;
    }

    /**
     * Gets the renamed local variables.
     * 

     *  In this method the we add the parametercount on the position of the variables from the method
     *  body. After that the correct order of the variables is rebuild according to the original ones.
     * 
     * @param programMethod the program method
     * @param variables the variables
     * @param parameterCount the parameter count
     * @param watchpoints the watchpoints
     * 
     * @return the renamed local variables
     */
    private static List<LocationVariable> addParameterCount(
            ProgramMethod programMethod, Map<Integer, SourceElement> variables,
            int parameterCount, List<WatchPoint> watchpoints) {

        Set<Entry<Integer, SourceElement>> entrySet = variables.entrySet();
        List<LocationVariable> localVariables = new LinkedList<LocationVariable>();

        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(programMethod)){
                for (int position : watchPoint.getKeyPositions()) {
                    for (Entry<Integer, SourceElement> entry : entrySet) {
                        if (entry.getKey().intValue() + parameterCount == position) {

                            VariableSpecification varspec = (VariableSpecification) entry.getValue();
                            localVariables.add((LocationVariable) varspec.getProgramVariable());
                        }
                    }
                }
            }
        }
        return localVariables;

    }

    private static Update buildNameUpdates(UpdateFactory uf,
            ListOfRenamingTable renamings, Node node, List<WatchPoint> watchpoints) {

        List<Update> nameUpdates = new LinkedList<Update>();
        IteratorOfRenamingTable i = renamings.iterator();

        for (WatchPoint watchPoint : watchpoints) {
            List<LocationVariable> orginialLocalVariables = watchPoint.getOrginialLocalVariables();
            List<LocationVariable> inittiallyRenamedLocalVariables = watchPoint.getInittiallyRenamedLocalVariables();
            assert orginialLocalVariables.size() == inittiallyRenamedLocalVariables.size();

            while (i.hasNext()) {
                RenamingTable renaming = i.next();
                for(int j = 0; j < orginialLocalVariables.size(); j++) {


                    LocationVariable originalVar = orginialLocalVariables.get(j);
                    LocationVariable initiallyRenamedVar = inittiallyRenamedLocalVariables.get(j);

                    System.out.println(originalVar.id() +" hashcode " + originalVar.hashCode());
                    System.out.println(initiallyRenamedVar.id());

                    SourceElement renamedVariable = renaming
                    .getRenaming(initiallyRenamedVar);
                    if (renamedVariable != null) {

                        System.out.println(renaming.toString());

                        Update elemtaryUpdate = uf.elementaryUpdate(
                                TermFactory.DEFAULT.createVariableTerm(originalVar),
                                TermFactory.DEFAULT.createVariableTerm((LocationVariable) renamedVariable)); 
                        System.out.println("update by tf"+elemtaryUpdate);

                        nameUpdates.add(elemtaryUpdate);
                        System.out.println("sizeof nameUpdates: " + nameUpdates.size());

                    }
                }
            }
        }


        try {

            return uf.parallel(nameUpdates.toArray(new Update[nameUpdates.size()]));
        } catch (RuntimeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

}
