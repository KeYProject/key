package de.uka.ilkd.key.util;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.Map.Entry;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
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
import de.uka.ilkd.key.visualdebugger.MethodVisitor;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
import de.uka.ilkd.key.visualdebugger.WatchPointManager;
import de.uka.ilkd.key.visualdebugger.WatchpointPO;
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
            ListOfTerm watchpoints, ETNode etn) {

        assert leafNodesInETNode != null;
        assert leafNodesInETNode.size() != 0 : "No node to process /in satisfiesWatchpoint /in WatchpointUtil";
        assert watchpoints != null;
        assert watchpoints.size() != 0 : "No watchpoint to evaluate /in satisfiesWatchpoint /in WatchpointUtil";

        LinkedList<Term> intersection = new LinkedList<Term>(Arrays
                .asList(watchpoints.toArray()));

        Term[] watches = watchpoints.toArray();
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
                            node.sequent(), pos, node.proof(), 250)) {
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
     * @param programPrefix
     * @return
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
            Sequent seq, PosInOccurrence pos, Proof proof, int maxsteps) {

        
        //start tracking names if necessary
        if(!WatchPointManager.getLocalVariables().isEmpty()){
            
            JavaInfo javaInfo = proof.getServices().getJavaInfo();
            getInitialRenamings(javaInfo, node);
            trackRenaming(javaInfo, node);
            }
        
        UpdateFactory updateFactory = new UpdateFactory(proof.getServices(),
                proof.simplifier());

        LinkedList<Update> updates = collectUpdates(pos);
        for (Update update : updates) {
            watchpoint = updateFactory.prepend(update, watchpoint);
        }
        ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
        seq = seq.changeFormula(newCF, pos).sequent();
        try {
            // start side proof
            final ProofStarter ps = new ProofStarter();
            final ProofEnvironment proofEnvironment = createProofEnvironment(seq,
                    proof, maxsteps, ps);
            System.out.println("14");

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
     * @param pos
     * @return
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

    /**
     * EvaluateWatchpoints.
     * 
     * Returns true, if the concatenation of all watchpoints by the junctor can
     * be evaluated to true, i.e. the proof can be closed
     * 
     * Example: watchpoints: w1, w2, w3 
     *              junctor: /\ (AND - logical conjunction) -> evaluates w1 /\ w2 /\ w3 
     *                       \/ (OR - logical disjunction) ->  evalutaes w1 \/ w2 \/ w3
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
            ListOfTerm watchpoints, Sequent seq, PosInOccurrence pos,
            Proof proof, Junctor junctor, boolean negateJunctor, int maxsteps) {

        if (watchpoints.isEmpty()) {
            return false;
        } else {
            if (watchpoints.size() == 1) {

                return WatchpointUtil.evalutateWatchpoint(node, watchpoints
                        .toArray()[0], seq, pos, proof, maxsteps);
            }
            //start tracking names if necessary
            if(!WatchPointManager.getLocalVariables().isEmpty()){
                
                JavaInfo javaInfo = proof.getServices().getJavaInfo();
                getInitialRenamings(javaInfo, node);
                trackRenaming(proof.getServices().getJavaInfo(), node);
            }
            
            UpdateFactory updateFactory = new UpdateFactory(
                    proof.getServices(), proof.simplifier());
            
            LinkedList<Update> updates = collectUpdates(pos);

            final TermFactory tf = TermFactory.DEFAULT;
            IteratorOfTerm iter = watchpoints.iterator();

            Term watchpoint = (Op.OR == junctor ? tf.createJunctorTerm(junctor,
                    iter.next(), tf.createJunctorTerm(Op.FALSE)) : tf
                    .createJunctorTerm(junctor, iter.next(), tf
                            .createJunctorTerm(Op.TRUE)));

            while (iter.hasNext()) {
                watchpoint = tf.createJunctorTerm(junctor, iter.next(),
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
            final ProofEnvironment proofEnvironment = createProofEnvironment(seq,
                    proof, maxsteps, ps);
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
     * @return
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
                        SLListOfTerm.EMPTY_LIST);
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
            ListOfTerm watchpoints) {
        System.out.println("setting watchpoints active...");
        try {
            for (ETNode node : nodes) {

                System.out.println("proofNodesInETNode: "
                        + node.getProofTreeNodes().size());
                HashSet<Node> leafNodesInETNode = getLeafNodesInETNode(node
                        .getProofTreeNodes().toArray());
                System.out.println("leafNodesInProofNodes: "
                        + leafNodesInETNode.size());
                boolean satisfiesWatchpoint = satisfiesWatchpoint(
                        leafNodesInETNode, watchpoints, node);
                node.setWatchpoint(satisfiesWatchpoint);
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

    public static Update trackRenaming(JavaInfo javaInfo, Node node) {

        HashSet<SourceElement> localVariables = WatchPointManager
        .getLocalVariables();
        
        if (localVariables.size() == 0)
            return null;
       
        System.out.println(localVariables.size() + " loc var size in WPU");
        //TODO traverse tree upwards
        ListOfRenamingTable renamingTables = node.getRenamingTable();
        if (renamingTables != null && renamingTables.size() > 0 ) {
        IteratorOfRenamingTable i = renamingTables.iterator();
        while (i.hasNext()) {
            System.out.println("++++++++");
            RenamingTable renaming = i.next();
            for (SourceElement variable : localVariables) {
                
                VariableSpecification varSpec = (VariableSpecification) variable;
                LocationVariable locationVariable = (LocationVariable) varSpec.getProgramVariable();
                
                    SourceElement renamedVariable = renaming.getRenaming(locationVariable);
                    
                    System.out.println("**************");
                    if (renamedVariable != null) {
                        System.out.println(" XXXXXXXXXXXXXXXXXXXXXXXXXXXXX");
//                        UpdateFactory uf = new UpdateFactory(null, null);
//                        Update elemtaryUpdate = uf.elementaryUpdate(null, null);
//                        // -> add el.Updates to list/array
//                        // -> create & return parallel update
//                        uf.parallel(null);

                    }
            }
            System.out.println(renaming.toString());
        }
        }
        return null;
    }

    public static HashSet<SourceElement> getInitialRenamings(JavaInfo javaInfo, Node node) {

        Node currentNode = node;
        Node parent = currentNode.parent();
        HashSet<SourceElement> renamedLocalVariables = new HashSet<SourceElement>();
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
                        MethodVisitor mbsVisitor = new MethodVisitor(mbs);
                        mbsVisitor.start();
                        programMethod = mbs
                                .getProgramMethod(javaInfo.getServices());
                        parameterCount = programMethod.getParameterDeclarationCount();
                        
//                        System.out.println("parametercount "
//                                + parameterCount);
//                        System.out.println("parameters "
//                                + programMethod.getParameterDeclarationAt(0));
//                        IProgramVariable programVariable = programMethod
//                                .getParameterDeclarationAt(0)
//                                .getVariableSpecification()
//                                .getProgramVariable();
//                        System.out.println("id "
//                                + ((LocationVariable) programVariable).id());

                        LinkedList<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod);
                        
                        for (Integer index : parameterIndices) {
                            renamedLocalVariables.add(programMethod.getParameterDeclarationAt(index));
                        }
                        
                    }
                    //treat currentnode, i.e. the method-frame 
                    SourceElement element = getStatement(currentNode);

                    if (element instanceof MethodFrame) {
                        MethodVisitor mv = new MethodVisitor(
                                (MethodFrame) element);
                        mv.start();
                        renamedLocalVariables.addAll(getRenamedLocalVariables(programMethod, valueToKey(mv.result()), parameterCount));
                        System.out.println("sizeof renamed vars " + renamedLocalVariables.size());
                        System.out.println(valueToKey(mv.result()));
                    }
                }
            }
            currentNode = parent;
            parent = currentNode.parent();
        }
        WatchPointManager.setLocalVariables(renamedLocalVariables);
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
        RuleSet expandRuleSet = new RuleSet(new Name("method_expand"));
        return listOfRuleSet.contains(expandRuleSet);
    }

    /**
     * Gets the indices of all parameters that are used in watchpoints for the given method.
     * 
     * @param programMethod the program method
     * 
     * @return the parameter indices of method, null if no local variables are used
     */
    private static LinkedList<Integer> getParameterIndicesOfMethod(
            ProgramMethod programMethod) {

        int parameterCount = programMethod.getParameterDeclarationCount();
        LinkedList<PositionWrapper> originalLocalVariables = WatchPointManager
                .getTemporaryLocalVariables();
        LinkedList<Integer> parameterIndices = new LinkedList<Integer>();
        if (originalLocalVariables.isEmpty() || originalLocalVariables == null) {
            return parameterIndices;
        } else {

            for (PositionWrapper positionWrapper : originalLocalVariables) {
                
                if (positionWrapper.getProgramMethod().equals(programMethod)
                        && positionWrapper.getPosition() < parameterCount) {
                    
                    parameterIndices.add(positionWrapper.getPosition());
                }
            }
            return parameterIndices;
        }
    }

    private static HashSet<SourceElement> getRenamedLocalVariables(ProgramMethod programMethod, Map<Integer, SourceElement> variables, int parameterCount) {
        
        Set<Entry<Integer, SourceElement>> entrySet = variables.entrySet();
        HashSet<SourceElement> localVariables = new HashSet<SourceElement>();
        LinkedList<PositionWrapper> originalLocalVariables = WatchPointManager
        .getTemporaryLocalVariables();
        for (Entry<Integer, SourceElement> entry : entrySet) {
            for (PositionWrapper positionWrapper : originalLocalVariables) {
                if(entry.getKey() + parameterCount == positionWrapper.getPosition() 
                        && positionWrapper.getProgramMethod().equals(programMethod)){
                    localVariables.add(entry.getValue());
                }
            }
        }
        return localVariables;


    }
}