/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.analysis;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.slicing.DependencyTracker;
import org.key_project.slicing.RuleStatistics;
import org.key_project.slicing.SlicingProofReplayer;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.util.ExecutionTime;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Results of the dependency analysis algorithm.
 *
 * @see DependencyTracker#analyze(boolean, boolean)
 * @author Arne Keller
 */
public final class AnalysisResults {
    /**
     * The analyzed proof.
     */
    public final Proof proof;
    public final DependencyGraph dependencyGraph;
    /**
     * Total amount of rule applications.
     */
    public final int totalSteps;
    /**
     * Amount of useful rule applications.
     */
    public final int usefulStepsNr;
    /**
     * Mapping of (rule display name)
     * to (total applications, useless applications, initial useless applications).
     */
    public final RuleStatistics ruleStatistics;
    /**
     * Set of useful proof steps.
     */
    public final Set<Node> usefulSteps;
    /**
     * Set of graph nodes required by useful rule applications.
     */
    public final Set<GraphNode> usefulNodes;
    /**
     * Set of branches in the proof guaranteed to be omitted in the proof slice.
     */
    public final Set<BranchLocation> uselessBranches;
    /**
     * Equal to size of {@link #uselessBranches}.
     */
    public final int usefulBranchesNr;
    /**
     * Branch stacks, as determined by the rule application de-duplication algorithm.
     */
    public final Map<Node, List<Node>> branchStacks;
    /**
     * Whether the dependency analysis algorithm ran.
     */
    public final boolean didDependencyAnalysis;
    /**
     * Whether the rule app de-duplication algorithm ran.
     */
    public final boolean didDeduplicateRuleApps;
    /**
     * Whether the rule app de-duplication algorithm performed was run in "aggressive" mode.
     */
    public final boolean didDeduplicateAggressive;
    /**
     * Execution timings of the analysis algorithms.
     */
    public final ExecutionTime executionTime;

    /**
     * Specify the results of analyzing a proof.
     *
     * @param proof the analyzed proof
     * @param dependencyGraph the dependency graph of the proof
     * @param totalSteps the number of steps in the proof
     * @param ruleStatistics statistics on analyzed rules
     * @param usefulSteps set of useful steps to include in the slice
     * @param usefulNodes set of useful graph nodes
     * @param uselessBranches set of useless branches
     * @param branchStacks branch stacks (see {@link SlicingProofReplayer} for details)
     * @param didDependencyAnalysis whether the dependency analysis algorithm ran
     * @param didDeduplicateRuleApps whether the rule de-duplication algorithm ran
     * @param executionTime timings
     */
    public AnalysisResults(
            Proof proof,
            DependencyGraph dependencyGraph,
            int totalSteps,
            RuleStatistics ruleStatistics,
            Set<Node> usefulSteps,
            Set<GraphNode> usefulNodes,
            Set<BranchLocation> uselessBranches,
            Map<Node, List<Node>> branchStacks,
            boolean didDependencyAnalysis,
            boolean didDeduplicateRuleApps,
            ExecutionTime executionTime) {
        this.proof = proof;
        this.dependencyGraph = dependencyGraph;
        this.totalSteps = totalSteps;
        this.usefulStepsNr = usefulSteps.size();
        this.ruleStatistics = ruleStatistics;
        this.usefulSteps = Collections.unmodifiableSet(usefulSteps);
        this.usefulNodes = Collections.unmodifiableSet(usefulNodes);
        this.uselessBranches = Collections.unmodifiableSet(uselessBranches);
        this.branchStacks = branchStacks;
        this.didDependencyAnalysis = didDependencyAnalysis;
        this.didDeduplicateRuleApps = didDeduplicateRuleApps;
        this.didDeduplicateAggressive =
            SlicingSettingsProvider.getSlicingSettings().getAggressiveDeduplicate(proof);
        this.executionTime = executionTime;
        this.usefulBranchesNr = (int) proof.allGoals().stream()
                .map(x -> x.node().getBranchLocation())
                .filter(this::branchIsUseful)
                .count();
    }

    /**
     * @param branchLocation branch location
     * @return whether that branch is marked as useless
     */
    public boolean branchIsUseful(BranchLocation branchLocation) {
        return uselessBranches.stream().noneMatch(branchLocation::hasPrefix);
    }

    /**
     * @return whether these analysis results suggest the proof can be sliced further
     */
    public boolean indicateSlicingPotential() {
        return totalSteps > usefulStepsNr;
    }

    /**
     * Reduce the sequent of the provided node to formulas deemed useful.
     * (Formulas are useful if they are used to close the branch.)
     *
     * @param node proof node
     * @return sequent with only useful formulas
     */
    public Sequent reduceSequent(Node node) {
        final Sequent seq = node.sequent();
        return JavaDLSequentKit.createSequent(reduce(seq.antecedent().asList(), node, true),
            reduce(seq.succedent().asList(), node, false));
    }

    private ImmutableList<SequentFormula> reduce(ImmutableList<SequentFormula> semi, Node node,
            boolean antec) {
        ImmutableList<SequentFormula> semiList = ImmutableSLList.nil();
        for (SequentFormula sf : semi) {
            var graphNode = dependencyGraph.getGraphNode(node.proof(), node.getBranchLocation(),
                new PosInOccurrence(sf, PosInTerm.getTopLevel(), antec));
            if (usefulNodes.contains(graphNode)) {
                semiList = semiList.prepend(sf);
            }
        }
        return semiList.size() == semi.size() ? semi : semiList.reverse();
    }

    @Override
    public String toString() {
        return "AnalysisResults{" +
            "totalSteps=" + totalSteps +
            ", usefulSteps=" + usefulStepsNr +
            ", ...}";
    }
}
