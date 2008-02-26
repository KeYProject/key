package de.uka.ilkd.key.util;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.strategy.DebuggerStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.visualdebugger.ProofStarter;
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

        LinkedList<Term> intersection = new LinkedList<Term>(Arrays
                .asList(watchpoints.toArray()));

        Term[] watches = watchpoints.toArray();
        System.out.println("watches computed for " + leafNodesInETNode.size()
                + " leafnodes..");
        for (Node node : leafNodesInETNode) {

            List<Term> temp = new LinkedList<Term>();
            PosInOccurrence pos = findPos(node);

            if (pos != null) {
                System.out.println("pos was not null!");
                for (Term watchpoint : watches) {

                    if (WatchpointUtil.evalutateWatchpoint(watchpoint, node
                            .sequent(), pos, node.proof(), 250)) {
                        temp.add(watchpoint);
                        System.out.println("wp evaluated to true");
                    }
                }
                intersection.retainAll(temp);
            }
            System.out
                    .println("wps evaluated to true (after intersection) for current node:"
                            + intersection.size());
        }
        etn.setWatchpointsSatisfied(intersection);
        System.out.println("LEAVING satisfiesWP...");
        return !intersection.isEmpty();
    }

    private static PosInOccurrence findPos(Node node) {

        System.out.println("findPos ...  ");
        Sequent seq = node.sequent();

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
            // if we find a update
            if (term.op() instanceof QuanUpdateOperator) {

                int targetPos = ((QuanUpdateOperator) term.op()).targetPos();
                pos = pos.down(targetPos);
                term = term.sub(targetPos);
                if (term.op() instanceof Modality) {
                    ProgramPrefix programPrefix = (ProgramPrefix) term
                            .javaBlock().program();

                    SourceElement firstStatement = PosInProgram.getProgramAt(
                            programPrefix.getFirstActiveChildPos(),
                            programPrefix).getFirstElement();

                    if (firstStatement.toString().startsWith("Debug.sep")) {
                        System.out.println("LEAVING findPos WITH result...");
                        return pos;
                    } else {
                        System.out.println("LEAVING findPos WITHOUT result...");
                        return null;
                    }
                } else {
                    throw new RuntimeException("IllegalStateException");
                }
            }
        }
        return null;
    }

    private static HashSet<Node> getLeavesInETNode(Node currentNode,
            List<Node> proofnodes) {

        HashSet<Node> result = new HashSet<Node>(3);
        IteratorOfNode iter = currentNode.childrenIterator();
        while (iter.hasNext()) {
            Node child = (Node) iter.next();
            if (proofnodes.contains(child)) {
                proofnodes.remove(child);
                result.addAll(getLeavesInETNode(child, proofnodes));
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
    public static boolean evalutateWatchpoint(Term watchpoint, Sequent seq,
            PosInOccurrence pos, Proof proof, int maxsteps) {

        if(proof == null) throw new NullPointerException("proof was null");
        if(pos == null) throw new NullPointerException("pos was null");
        System.out.println("maxsteps : " + maxsteps);
        if(watchpoint == null) throw new NullPointerException("watchpoint was null");
        if(seq == null) throw new NullPointerException("seq was null");
      
        LinkedList<Update> updates = new LinkedList<Update>();
        UpdateFactory updateFactory = new UpdateFactory(proof.getServices(),
                proof.simplifier());
        // collect all updates
        PIOPathIterator it = pos.iterator();
        while (it.hasNext()) {
            it.next();
            Term term = it.getSubTerm();
            Operator operator = term.op();
            if (operator instanceof QuanUpdateOperator) {

                Update update = Update.createUpdate(term);
                System.out.println("evaluateWP.update.toString: " + update.toString());
                updates.addFirst(update);
            }
        }
        System.out.println("evaluateWP:collected updates...");
        for (Update update : updates) {
            watchpoint = updateFactory.prepend(update, watchpoint);
        }
        System.out.println("evaluateWP:builded wp terms..." + watchpoint.toString());
        ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
        System.out.println("1");
        seq = seq.changeFormula(newCF, pos).sequent();
        System.out.println("2");
        try{
        // start side proof
        ProofStarter ps = new ProofStarter();
        ProofEnvironment proofEnvironment = proof.env();
        InitConfig initConfig = proofEnvironment.getInitConfig();
        WatchpointPO watchpointPO = new WatchpointPO("WatchpointPO", seq);
        System.out.println("6");
        watchpointPO.setIndices(initConfig.createTacletIndex(), initConfig
                .createBuiltInRuleIndex());
        System.out.println("7");
        StrategyProperties strategyProperties = DebuggerStrategy
                .getDebuggerStrategyProperties(true, false, false,
                        SLListOfTerm.EMPTY_LIST);
        System.out.println("8");
        final StrategyFactory factory = new DebuggerStrategy.Factory();
        Strategy strategy = (factory.create(proof, strategyProperties));
        watchpointPO.setProofSettings(proof.getSettings());
        watchpointPO.setInitConfig(initConfig);
        ps.setStrategy(strategy);
        ps.setMaxSteps(maxsteps);
        ps.init(watchpointPO);
        System.out.println("14");
        if(strategy == null) throw new NullPointerException("strategy was null");
        if(watchpointPO == null) throw new NullPointerException("watchpointPO was null");
        if(proof.getSettings() == null) throw new NullPointerException("settings was null");
        ps.run(proofEnvironment);
        System.out.println("LEAVING evaluateWP...");
        return ps.getProof().closed();}
        catch(Throwable t){
            System.out.println(t.toString());
            t.printStackTrace();
        }
        return false;
    }

    /**
     * EvaluateWatchpoints.
     * 
     * Returns true, if the concatenation of all watchpoints by the junctor can
     * be evaluated to true, i.e. the proof can be closed
     * 
     * Example: watchpoints: w1, w2, w3 junctor: /\ (AND - logical conjunction) ->
     * evaluates w1 /\ w2 /\ w3 \/ (OR - logical disjunction) -> evalutaes w1 \/
     * w2 \/ w3
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
    public static boolean evalutateWatchpoints(ListOfTerm watchpoints,
            Sequent seq, PosInOccurrence pos, Proof proof, Junctor junctor,
            boolean negateJunctor, int maxsteps) {

        if (watchpoints.isEmpty()) {
            return false;
        } else {
            if (watchpoints.size() == 1) {

                return WatchpointUtil.evalutateWatchpoint(
                        watchpoints.toArray()[0], seq, pos, proof, maxsteps);
            }

            LinkedList<Update> updates = new LinkedList<Update>();

            UpdateFactory updateFactory = new UpdateFactory(
                    proof.getServices(), proof.simplifier());
            // collect all updates
            PIOPathIterator it = pos.iterator();
            while (it.hasNext()) {
                it.next();
                Term term = it.getSubTerm();
                Operator operator = term.op();
                if (operator instanceof QuanUpdateOperator) {

                    Update update = Update.createUpdate(term);
                    System.out.println("update.toString: " + update.toString());
                    updates.addFirst(update);
                }
            }

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
            ProofStarter ps = new ProofStarter();
            ProofEnvironment proofEnvironment = proof.env();
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
            ps.run(proofEnvironment);

            return ps.getProof().closed();
        }
    }

    /**
     * getAllLeaveNodes() returns all ETNodes that are leaves in the current
     * ExecutionTree, which is passed as ETNode as well.
     * 
     * 
     * @return a LinkedList containing all leaves of the current ET
     */
    public static LinkedList<ETNode> getAllLeafETNodes(ETNode etn) {

        System.out.println("getting the leavenodes...");
        LinkedList<ETNode> leaves = new LinkedList<ETNode>();
        LinkedList<ETNode> children = etn.getChildrenList();

        if (children.size() == 0) {
            leaves.add(etn);
            return leaves;
        } else {
            for (ETNode node : children) {
                // the results of the recursive calls must be stored
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

        // create a collection from the array -> type conversion
        // since getProofTreeNodes() only returns a ListOfNode which
        // does not implement the Collection interface
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
            candidates.addAll(getLeavesInETNode(currentNode, proofnodes));
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
                
                HashSet<Node> leafNodesInETNode = getLeafNodesInETNode(node.getProofTreeNodes().toArray());
                System.out.println("leafNodesINETNODE: "+ leafNodesInETNode.size());
                boolean satisfiesWatchpoint = satisfiesWatchpoint(
                        leafNodesInETNode,
                        watchpoints, node);
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
}