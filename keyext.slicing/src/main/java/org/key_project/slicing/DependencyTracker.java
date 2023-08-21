/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.proofevent.NodeChangeAddFormula;
import de.uka.ilkd.key.proof.proofevent.NodeChangeRemoveFormula;
import de.uka.ilkd.key.proof.proofevent.NodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleAppUtil;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.slicing.analysis.DependencyAnalyzer;
import org.key_project.slicing.graph.AddedRule;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.DotExporter;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.PseudoInput;
import org.key_project.slicing.graph.PseudoOutput;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * Tracks proof steps as they are applied on the proof.
 * Each proof step is recorded in the dependency graph ({@link DependencyGraph}).
 *
 * @author Arne Keller
 */
public class DependencyTracker implements RuleAppListener, ProofTreeListener {
    /**
     * The proof this tracker monitors.
     */
    private final Proof proof;
    /**
     * The dependency graph this tracker creates.
     */
    private final DependencyGraph graph = new DependencyGraph();
    /**
     * Collection of dynamically added rules.
     * For each new taclet, the dependency graph node representing that rule is stored in the map.
     */
    private final Map<Taclet, AddedRule> dynamicRules = new IdentityHashMap<>();
    /**
     * Cached analysis results.
     *
     * @see DependencyAnalyzer
     */
    private AnalysisResults analysisResults = null;

    /**
     * Construct a new tracker for a proof.
     * This tracker is added as a RuleAppListener and ProofTreeListener to the proof.
     *
     * @param proof the proof to track
     */
    public DependencyTracker(Proof proof) {
        this.proof = proof;
        proof.addRuleAppListener(this);
        proof.addProofTreeListener(this);
        proof.register(this, DependencyTracker.class);
    }

    /**
     * Compute the sequent formulas used by the provided rule application:
     * instantiations for \find, \assume, etc.
     *
     * @param ruleApp a rule application
     * @param node node corresponding to the rule application
     * @return all formulas used by the rule application
     */
    private static Set<PosInOccurrence> inputsOfRuleApp(RuleApp ruleApp, Node node) {
        Set<PosInOccurrence> inputs = new HashSet<>();
        if (ruleApp.posInOccurrence() != null) {
            inputs.add(ruleApp.posInOccurrence().topLevel());
        }
        inputs.addAll(RuleAppUtil.ifInstsOfRuleApp(ruleApp, node));
        return inputs;
    }

    /**
     * Get the inputs required by a proof step. Includes the used taclet, if it was added by
     * another previous proof step. Always includes the sequent formulas used to instantiate
     * the \find and \assumes pattern.
     *
     * @param n node
     * @param removed formulas removed by this node
     * @return pairs of graph nodes and whether the graph node was removed
     */
    private List<Pair<GraphNode, Boolean>> inputsOfNode(Node n, Set<PosInOccurrence> removed) {
        RuleApp ruleApp = n.getAppliedRuleApp();
        List<Pair<GraphNode, Boolean>> input = new ArrayList<>();

        // check whether the rule of this proof step was added by another proof step
        // -> if so, add that dynamically added taclet as a dependency
        Rule rule = n.getAppliedRuleApp().rule();
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            if (taclet.getAddedBy() != null) {
                input.add(new Pair<>(dynamicRules.get(taclet), false));
            }
        }

        // record sequent formula inputs
        for (PosInOccurrence in : inputsOfRuleApp(ruleApp, n)) {
            // Need to find the graph node corresponding to the used sequent formula in the graph.
            // Requires knowing the branch it was produced in.
            // Try the branch location of this proof step first, then check the previous branches.
            BranchLocation loc = n.getBranchLocation();
            int size = loc.size();
            boolean added = false;
            for (int i = 0; i <= size; i++) {
                TrackedFormula formula =
                    new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(),
                        proof.getServices());
                if (graph.containsNode(formula)) {
                    input.add(new Pair<>(formula, removed.contains(in)));
                    added = true;
                    break;
                }
                if (loc.size() > 0) {
                    loc = loc.removeLast();
                }
            }
            if (!added) {
                // should only happen if the formula is the initial proof obligation
                if (!proof.root().sequent().contains(in.sequentFormula())) {
                    throw new IllegalStateException(
                        "found formula that was not produced by any rule! " + in.sequentFormula());
                }
                TrackedFormula formula =
                    new TrackedFormula(in.sequentFormula(), loc, in.isInAntec(),
                        proof.getServices());
                input.add(new Pair<>(formula, removed.contains(in)));
            }
        }

        return input;
    }

    /**
     * Get all formulas removed by the provided rule application, i.e. all formulas not present
     * in the replacement nodes.
     *
     * @param ruleAppInfo some rule application
     * @return formulas removed by that rule application
     */
    private Set<PosInOccurrence> formulasRemovedBy(RuleAppInfo ruleAppInfo) {
        Set<PosInOccurrence> removed = new HashSet<>();
        for (NodeReplacement newNode : ruleAppInfo.getReplacementNodes()) {
            newNode.getNodeChanges().forEachRemaining(nodeChange -> {
                if (nodeChange instanceof NodeChangeRemoveFormula) {
                    removed.add(nodeChange.getPos());
                }
            });
        }
        return removed;
    }

    /**
     * Get the formulas added by this rule application. Each returned pair is one formula
     * and the ID of the branch it is added to (-1 if the node doesn't branch).
     *
     * @param ruleAppInfo rule application info
     * @return formulas added
     */
    private List<Pair<PosInOccurrence, Integer>> outputsOfNode(RuleAppInfo ruleAppInfo) {
        List<Pair<PosInOccurrence, Integer>> outputs = new ArrayList<>();
        int sibling = ruleAppInfo.getReplacementNodes().size() - 1;
        for (NodeReplacement b : ruleAppInfo.getReplacementNodes()) {
            int id = ruleAppInfo.getReplacementNodes().size() > 1 ? sibling : -1;
            b.getNodeChanges().forEachRemaining(c -> {
                if (c instanceof NodeChangeAddFormula) {
                    outputs.add(new Pair<>(c.getPos(), id));
                }
            });
            sibling--;
        }
        return outputs;
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        if (e.getSource() != proof) {
            throw new IllegalStateException(
                "dependency tracker received rule application on wrong proof");
        }
        RuleAppInfo ruleAppInfo = e.getRuleAppInfo();
        RuleApp ruleApp = ruleAppInfo.getRuleApp();
        ImmutableList<Goal> goalList = e.getNewGoals();
        Node n = ruleAppInfo.getOriginalNode();

        // outputs: new graph nodes
        List<GraphNode> output = new ArrayList<>();

        // record any rules added by this rule application
        for (NodeReplacement newNode : ruleAppInfo.getReplacementNodes()) {
            for (NoPosTacletApp newRule : newNode.getNode().getLocalIntroducedRules()) {
                if (newRule.rule() instanceof Taclet
                        && ((Taclet) newRule.rule()).getAddedBy() == n) {
                    AddedRule ruleNode = new AddedRule(newRule.rule().name().toString());
                    output.add(ruleNode);
                    dynamicRules.put((Taclet) newRule.rule(), ruleNode);
                }
            }
        }

        // record removed (replaced) input formulas
        // (these are the same for each new branch)
        Set<PosInOccurrence> removed = formulasRemovedBy(ruleAppInfo);

        // inputs: (graph node, whether that graph node was replaced)
        List<Pair<GraphNode, Boolean>> input = inputsOfNode(n, removed);

        // Newly created sequent formulas and the index of the branch they are created in.
        // If no new branches are created, use index -1.
        List<Pair<PosInOccurrence, Integer>> outputs = outputsOfNode(ruleAppInfo);

        for (Pair<PosInOccurrence, Integer> out : outputs) {
            BranchLocation loc = n.getBranchLocation();
            if (out.second != -1) {
                // this is a branching proof step: set correct branch location of new formulas
                loc = loc.append(new Pair<>(n, out.second));
            }
            TrackedFormula formula = new TrackedFormula(
                out.first.sequentFormula(),
                loc,
                out.first.isInAntec(),
                proof.getServices());
            output.add(formula);
        }

        // add closed goals to output nodes
        if (goalList.isEmpty() || (ruleApp instanceof TacletApp &&
                ((TacletApp) ruleApp).taclet().closeGoal())) {
            // closed goal is always the next node
            // (or the current node, if the goal was closed by SMT)
            Node closedGoal = n.childrenCount() > 0 ? n.child(0) : n;
            output.add(
                new ClosedGoal(closedGoal.serialNr(), n.getBranchLocation()));
        }

        n.register(new DependencyNodeData(
            input,
            output,
            ruleApp.rule().displayName() + "_" + n.serialNr()), DependencyNodeData.class);

        // add pseudo nodes so the rule application is always included in the graph
        if (input.isEmpty()) {
            input.add(new Pair<>(new PseudoInput(), true));
        }
        if (output.isEmpty()) {
            output.add(new PseudoOutput());
        }

        // add new edges to graph
        graph.addRuleApplication(n, input, output);
    }

    @Override
    public void proofIsBeingPruned(ProofTreeEvent e) {
        // clean up removed formulas / nodes /...
        analysisResults = null;
        graph.prune(e.getNode());
    }

    /**
     * Export the dependency graph created by this tracker in DOT format.
     * See {@link DotExporter}.
     *
     * @param abbreviateFormulas whether to shorten formula labels
     * @return DOT string
     */
    public String exportDot(boolean abbreviateFormulas) {
        return DotExporter.exportDot(proof, graph, analysisResults, abbreviateFormulas);
    }

    /**
     * Export part of the dependency graph around a specific graph node.
     *
     * @param abbreviateFormulas whether to shorten formula labels
     * @param omitBranch whether to omit branch labels
     * @param node graph node to center export around
     * @return DOT string
     */
    public String exportDotAround(boolean abbreviateFormulas, boolean omitBranch, GraphNode node) {
        return DotExporter.exportDotAround(
            graph, analysisResults, abbreviateFormulas, omitBranch, node);
    }

    /**
     * Analyze the tracked proof using one or both analysis algorithms.
     * Returns null if the proof is not closed.
     *
     * @param doDependencyAnalysis whether to apply the dependency analysis algorithm
     * @param doDeduplicateRuleApps whether to de-duplicate rule applications
     * @return analysis results (null if proof is not closed)
     */
    public AnalysisResults analyze(boolean doDependencyAnalysis, boolean doDeduplicateRuleApps) {
        if (analysisResults != null
                && analysisResults.didDependencyAnalysis == doDependencyAnalysis
                && analysisResults.didDeduplicateRuleApps == doDeduplicateRuleApps
                && analysisResults.didDeduplicateAggressive == SlicingSettingsProvider
                        .getSlicingSettings().getAggressiveDeduplicate(proof)) {
            return analysisResults;
        }
        analysisResults = new DependencyAnalyzer(
            proof, graph, doDependencyAnalysis, doDeduplicateRuleApps).analyze();
        return analysisResults;
    }

    /**
     * Get the proof step that added a sequent formula to the proof.
     *
     * @param currentNode the proof node that contains <code>pio</code>
     * @param pio a sequent formula
     * @return the node that added this formula, or null
     */
    public Node getNodeThatProduced(Node currentNode, PosInOccurrence pio) {
        if (proof == null) {
            return null;
        }
        GraphNode graphNode = graph.getGraphNode(proof, currentNode.getBranchLocation(), pio);
        Stream<Node> incoming = graph.incomingEdgesOf(graphNode);
        return incoming.findFirst().orElse(null);
    }

    /**
     * Get the analysis results previously computed.
     *
     * @return analysis results or null (if not yet computed)
     */
    public AnalysisResults getAnalysisResults() {
        return analysisResults;
    }

    /**
     * @return the dependency graph populated by this tracker
     */
    public DependencyGraph getDependencyGraph() {
        return graph;
    }
}
