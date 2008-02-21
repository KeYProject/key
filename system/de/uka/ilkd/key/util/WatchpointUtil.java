package de.uka.ilkd.key.util;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentSkipListSet;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
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
import de.uka.ilkd.key.visualdebugger.WatchPoint;
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
        System.out.println("size of ETNode-leaves: " + leaves.size());
        return leaves;

    }

    /**
     * setActiveWatchpoints
     * 
     * @param nodes -
     *                a list of (leaf-)ETNodes of the current ET
     */
    public static void setActiveWatchpoint(List<ETNode> nodes,
            ListOfTerm watchpoints) {
        System.out.println("setting watchpoints active...");
        for (ETNode node : nodes) {
            node.setWatchpoint(satisfiesWatchpoint(getLeafNodesInETNode(node
                    .getProofTreeNodes().toArray()), watchpoints));
        }
    }

    /**
     * satisfiesWatchpoint returns true, if all leaf nodes in this ETNode
     * satisfy at least one watchpoint from the list
     */
    private static boolean satisfiesWatchpoint(HashSet<Node> leafNodesInETNode,
            ListOfTerm watchpoints) {

        List<Term> intersection = new LinkedList<Term>(Arrays
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
        }
        System.out.println("wp evaluated to false");
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
                    System.out.println("ProgramPrefix : "
                            + programPrefix.toString());

                    SourceElement firstStatement = PosInProgram.getProgramAt(
                            programPrefix.getFirstActiveChildPos(),
                            programPrefix).getFirstElement();

                    if (firstStatement.toString().startsWith("Debug.sep")) {
                        return pos;
                    } else {
                        return null;
                    }
                } else {
                    throw new RuntimeException("IllegalStateException");
                }
            }
        }
        return null;
    }

    /**
     * getAllLeafNodes
     * 
     * @param nodes -
     *                a list of (leaf-)ETNodes of the current ET
     * @return leaves - a LinkedList with all
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
     * @return true if the watchpoint is satisfied in the current state
     */
    public static boolean evalutateWatchpoint(Term watchpoint, Sequent seq,
            PosInOccurrence pos, Proof proof, int maxsteps) {

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
                System.out.println("update.toString: " + update.toString());
                updates.addFirst(update);
            }
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

    /**
     * EvaluateWatchpoints.
     * 
     * Returns true, if all of the watchpoints (logical conjunction) contained
     * in the passed list can be evaluated to true in the current program state.
     */
    public static boolean evalutateWatchpoints(ListOfTerm watchpoints,
            Sequent seq, PosInOccurrence pos, Proof proof, Junctor junctor,
            int maxsteps) {

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
}