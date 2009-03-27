// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.lang.reflect.InvocationTargetException;
import java.util.*;
import java.util.Map.Entry;

import javax.swing.SwingUtilities;

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
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;

/**
 * The Class WatchpointUtil.
 * 
 * This Class offers some tools to identify and mark Watchpoints in the current
 * program state, respectivly in the ExecutionTree ET.
 */
public class WatchpointUtil {

    private static final int ALL = 1;
    /**
     * satisfiesWatchpoint returns true, if all leaf nodes in this ETNode
     * satisfy at least one watchpoint from the list.
     * 
     * @param leafNodesInETNode the leaf nodes in et node
     * @param watchpoints the watchpoints
     * @param etn the etn
     * 
     * @return true, if satisfies watchpoint
     */
    private static boolean satisfiesWatchpoint(HashSet<Node> leafNodesInETNode,
            List<WatchPoint> watchpoints, ETNode etn) {

        assert leafNodesInETNode != null;
        assert leafNodesInETNode.size() != 0 : "No node to process /in satisfiesWatchpoint /in WatchpointUtil";
        assert watchpoints != null;
        assert watchpoints.size() != 0 : "No watchpoint to evaluate /in satisfiesWatchpoint /in WatchpointUtil";

        List<WatchPoint> intersection = watchpoints;
        System.out.println("watches computed for " + leafNodesInETNode.size()
                + " leafnodes..");
        for (Node node : leafNodesInETNode) {

            List<WatchPoint> temp = new LinkedList<WatchPoint>();

            PosInOccurrence pos = findPos(node.sequent().succedent());
            if (pos == null)
                pos = findPos(node.sequent().antecedent());

            if (pos != null) {
                for (WatchPoint watchpoint : watchpoints) {

                    if (WatchpointUtil.evalutateWatchpoint(node, watchpoint,
                            node.sequent(), pos, node.proof(), 250, watchpoints)) {
                        temp.add(watchpoint);
                        System.out.println("wp true in subset");
                        etn.addWatchpointTrueInSubset(watchpoint);
                    }
                }
            }
            intersection.retainAll(temp);
            System.out
            .println("wps evaluated to true (after intersection) for current node:"
                    + intersection.size());
        }
        etn.setWatchpointsSatisfied(intersection);
        return !intersection.isEmpty();
    }

    /**
     * Finds the PosInOccurrence.
     * 
     * This method looks for the PosInOccurrence in the given semisequent,
     * which should be obtained from a proof node.
     * That allows us to check if a watchpoint is true at an arbitrary node in 
     * the proof tree, even if we proceeded with symbolic execution. 
     * 
     * @param seq the seq
     * 
     * @return the pos in occurrence
     */
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
                    return pos;
                } else {
                    continue;
                }
            }
        }
        System.out.println("LEAVING findPos WITHOUT result...");
        return null;
    }

    /**
     * Gets the first active statement.
     * The method returns the first active statement within the modality.
     * It simply steps over the program prefix.
     * 
     * @param term the term
     * 
     * @return the first active statement
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

    /**
     * Find leaves.
     * 
     * @param currentNode the current node
     * @param proofnodes the proofnodes
     * 
     * @return the hash set< node>
     */
    private static boolean hasChildrenInSet(Node currentNode,
            List<Node> proofnodes) {

        IteratorOfNode iter = currentNode.childrenIterator();
        while (iter.hasNext()) {
            Node child = (Node) iter.next();
            if (proofnodes.contains(child)) {
               return true;
            }
        }
        return false;
    }

    /**
     * EvaluateWatchpoint.
     * 
     * Evaluates a single watchpoint.
     * 
     * @param node the node
     * @param watchpoint the watchpoint
     * @param seq the seq
     * @param pos the pos
     * @param proof the proof
     * @param maxsteps the maxsteps
     * @param watchpoints the watchpoints
     * 
     * @return true, if the watchpoint is satisfied in the current state
     */
    public static boolean evalutateWatchpoint(Node node, WatchPoint watchpoint,
            Sequent seq, PosInOccurrence pos, Proof proof, int maxsteps,
            List<WatchPoint> watchpoints) {

        System.out.println(watchpoint.getRawTerm());
        if(!watchpoint.isEnabled()) return false;
        VariableNameTracker vnt = new VariableNameTracker(node, watchpoints);
        vnt.start();
        if(watchpoint.isLocal() && !vnt.getActiveMethod().equals(watchpoint.getProgramMethod())) return false;
       
        TermBuilder tb = TermBuilder.DF;
        UpdateFactory updateFactory = new UpdateFactory(proof.getServices(),
                proof.simplifier());

        LinkedList<Update> updates = new LinkedList<Update>();

        composeWatchpointTerm(node, watchpoint, vnt, tb, updateFactory, updates);
        
        Term wp = watchpoint.getComposedTerm();
        updates.addAll(collectUpdates(pos));
        for (Update update : updates) {
            wp = updateFactory.prepend(update, wp);
        }
        System.out.println("++++++ starting side proof with watchpoint: "+wp);
        boolean result = startSideProof(seq, pos, proof, maxsteps, wp);
        if (!watchpoint.testPossible()) {
            return result;
        } else {
            //if already true, do not bother
            if(result) return result;
            wp = tb.not(wp);
            return !startSideProof(seq, pos, proof, maxsteps, wp);
        }
    }

    /**
     * @param node
     * @param watchpoint
     * @param tb
     * @param updateFactory
     * @param updates
     */
    private static void composeWatchpointTerm(Node node, WatchPoint watchpoint,
            VariableNameTracker vnt, TermBuilder tb,
            UpdateFactory updateFactory, LinkedList<Update> updates) {
        
        Term wp;
        // start tracking names if necessary (local watchpoints)
        if (watchpoint.isLocal()) {

            updates.add(buildNameUpdates(updateFactory, vnt.result()));
            updates.add(updateSelfVar(updateFactory, watchpoint, vnt
                    .getSelfVar()));
            watchpoint.setComposedTerm(watchpoint.getRawTerm());
        } else {
            LogicVariable lv = new LogicVariable(new Name(watchpoint.getSelf()
                    .name()+ "_lv"), watchpoint.getSelf().getKeYJavaType().getSort());
            //update self variable
            watchpoint.setComposedTerm(updateFactory.prepend(updateFactory
                    .elementaryUpdate(
                            TermFactory.DEFAULT.createVariableTerm(watchpoint.getSelf()),
                            TermFactory.DEFAULT.createVariableTerm(lv)),watchpoint.getRawTerm()));
            
            wp = watchpoint.getComposedTerm();
            // quantify term
            if (watchpoint.getFlavor() == ALL) {
                watchpoint.setComposedTerm(tb.all(lv, wp));
            } else {
                watchpoint.setComposedTerm(tb.ex(lv, wp));
            }
        }
    }

    /**
     * @param seq
     * @param pos
     * @param proof
     * @param maxsteps
     * @param wp
     */
    private static boolean startSideProof(Sequent seq, PosInOccurrence pos,
            Proof proof, int maxsteps, Term wp) {
        ConstrainedFormula newCF = new ConstrainedFormula(wp);
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
            return ps.getProof().closed();
            
        } catch (Throwable t) {
            t.printStackTrace();
        }
        return false;
    }

    /**
     * updateSelfVar updates the self variable of a local watchpoint.
     * 
     * @param uf
     * @param watchpoint
     * @param selfVar
     * @return Update
     */
    private static Update updateSelfVar(UpdateFactory uf, WatchPoint watchpoint,
            SourceElement selfVar) {
        // handle static methods
        if (selfVar == null) {
            return uf.skip();
        }
        return uf.elementaryUpdate(
                TermFactory.DEFAULT.createVariableTerm(watchpoint.getSelf()),
                TermFactory.DEFAULT.createVariableTerm((LocationVariable) selfVar)); 
    }

    /**
     * Collect updates.
     * The method collects all updated that can be found in front of the modality
     * to preserve the current state.
     * 
     * @param pos the pos
     * 
     * @return the linked list< update>
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
     * EvaluateWatchpoints. TODO out of order - currently not working
     * 
     * Returns true, if the concatenation of all watchpoints by the junctor can
     * be evaluated to true, i.e. the proof can be closed
     *  
     * Example:
     * watchpoints: w1, w2, w3
     * junctor: /\ (AND - logical conjunction) -> evaluates w1 /\ w2 /\ w3
     *          \/ (OR  - logical disjunction) -> evalutaes w1 \/ w2 \/ w3
     * 
     * @param watchpoints -
     * a list of all watchpoints that have to be taken into account
     * @param seq - the sequent
     * @param pos - the PosInOcc
     * @param proof - the proof
     * @param junctor -the junctor to use
     * @param negateJunctor - set this to true, if you want to realize NOR/NAND concatenation
     * @param maxsteps - the upper bound of steps that should be applied to close the proof
     * @param node the node
     * 
     * @return true, if the watchpoint formula evaluates to true (according to concatenation)
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
                return WatchpointUtil.evalutateWatchpoint(node, wp, seq, pos, proof, maxsteps, watchpoints);
            }

            VariableNameTracker vnt = new VariableNameTracker(node,
                    watchpoints);           
            for (WatchPoint wp : watchpoints) {
                if(wp.isEnabled()) {
                    composeWatchpointTerm(node, wp, vnt, TermBuilder.DF, updateFactory, updates);
                }
            }
            updates.addAll(collectUpdates(pos));

            final TermFactory tf = TermFactory.DEFAULT;
            Iterator<WatchPoint> iter = watchpoints.iterator();

            Term watchpoint = (Op.OR == junctor ? tf.createJunctorTerm(junctor,
                    ((WatchPoint)iter.next()).getComposedTerm(), tf.createJunctorTerm(Op.FALSE)) : tf
                    .createJunctorTerm(junctor, ((WatchPoint)iter.next()).getComposedTerm(), tf
                            .createJunctorTerm(Op.TRUE)));

            while (iter.hasNext()) {
                watchpoint = tf.createJunctorTerm(junctor, ((WatchPoint)iter.next()).getComposedTerm(),
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
     * Creates the proof environment.
     * 
     * @param seq the seq
     * @param proof the proof
     * @param maxsteps the maxsteps
     * @param ps the ps
     * 
     * @return the proof environment
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
     * @param etn the etn
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
     * getAllLeafNodes.
     * 
     * @param nodes -
     * an array containing all (proof)nodes of an ETNode
     * 
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
        HashSet<Node> result = new HashSet<Node>(INITIALCAPACITY);
        
        while (!proofnodes.isEmpty()) {

            Node currentNode = proofnodes.get(0);
            proofnodes.remove(currentNode);
            
            if(!hasChildrenInSet(currentNode, proofnodes)){
                result.add(currentNode);
            }
            Node parentNode = currentNode.parent();
            while (parentNode != null && proofnodes.contains(parentNode)) {
                proofnodes.remove(parentNode);
                parentNode = parentNode.parent();

            }
        }
        System.out.println("result.size: " + result.size());
        return result;
    }

    /**
     * setActiveWatchpoints.
     * 
     * @param nodes -
     * a list of ETNodes of the current ET. The watchpoints will
     * be evaluated for all these nodes.
     * @param watchpoints the watchpoints
     */
    public static void setActiveWatchpoint(List<ETNode> nodes,
            List<WatchPoint> watchpoints) {
        try {
            for (ETNode node : nodes) {

                HashSet<Node> leafNodesInETNode = getLeafNodesInETNode(node
                        .getProofTreeNodes().toArray());

                node.setWatchpoint(satisfiesWatchpoint(
                        leafNodesInETNode, watchpoints, node));
            }
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * Gets the executiontree as list. The method works top-down, 
     * so pass the root node of the (sub) tree you need as list.
     * 
     * @param etn the ETNode containing the current ET
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

    /**
     * Value to key.
     * Swaps the values of the given map to its keys.
     * 
     * @param map the map
     * 
     * @return the hash map< integer, source element>
     */
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

    /**
     * Builds the name updates.
     * 
     * This method finally updates all names of local variables that were used in 
     * watchpoints to their current name.
     * 
     * @param uf the uf
     * @param nameMaps the name maps
     * 
     * @return the update
     */
    private static Update buildNameUpdates(UpdateFactory uf,
            Map<ProgramMethod, ListOfRenamingTable> nameMaps) {

        List<Update> nameUpdates = new LinkedList<Update>();
        System.out.println(nameMaps);
        for (ListOfRenamingTable lort : nameMaps.values()) {

            if(!lort.isEmpty()){
                RenamingTable lastRT = lort.head();
                Iterator<LocationVariable> it = lastRT.getRenamingIterator();

                while(it.hasNext()){
                    LocationVariable originalVar = (LocationVariable) it.next();

                    LocationVariable locationVariable = (LocationVariable) lastRT.getHashMap().get(originalVar);
                    Update elemtaryUpdate = uf.elementaryUpdate(
                            TermFactory.DEFAULT.createVariableTerm(originalVar),
                            TermFactory.DEFAULT.createVariableTerm(locationVariable)); 
                    System.out.println(originalVar.id() +" -> " + locationVariable.id());
                    System.out.println(elemtaryUpdate);
                    nameUpdates.add(elemtaryUpdate);}
            }
        }
        return uf.parallel(nameUpdates.toArray(new Update[nameUpdates.size()]));
    }

}
