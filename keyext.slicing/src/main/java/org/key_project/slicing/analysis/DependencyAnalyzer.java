/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.analysis;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.CloseAfterMergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.SMTRuleApp;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.DependencyNodeData;
import org.key_project.slicing.RuleStatistics;
import org.key_project.slicing.SlicingSettingsProvider;
import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.ClosedGoal;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.TrackedFormula;
import org.key_project.slicing.util.ExecutionTime;
import org.key_project.util.EqualsModProofIrrelevancyWrapper;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implementation of both proof analysis algorithms.
 *
 * @author Arne Keller
 */
public final class DependencyAnalyzer {
    /**
     * Execution timings key for total time taken by the analyzer.
     */
    private static final String TOTAL_WORK = "0 (total time)";
    /**
     * Execution timings key for time required to caclculate {@link RuleStatistics}.
     */
    private static final String STATISTICS = "~ Statistical data gathering";
    /**
     * Execution timings key for time taken by the first analysis algorithm.
     */
    private static final String DEPENDENCY_ANALYSIS = "1 Dependency Analysis";
    /**
     * Execution timings key for time taken to run the first phase of the dependency analysis.
     */
    private static final String DEPENDENCY_ANALYSIS2 =
        "1a Dependency Analysis: search starting @ closed goals";
    /**
     * Execution timings key for time taken to run the cut analysis phase of the dependency
     * analysis.
     */
    private static final String DEPENDENCY_ANALYSIS3 =
        "1b Dependency Analysis: analyze branching nodes";
    /**
     * Execution timings key for time taken to mark steps in eliminated branches as useless.
     */
    private static final String DEPENDENCY_ANALYSIS4 =
        "1c Dependency Analysis: final mark of useless steps";
    /**
     * Execution timings key for time taken to run the de-duplication algorithm.
     */
    private static final String DUPLICATE_ANALYSIS = "2 Duplicate Analysis";
    /**
     * Execution timings key for time taken to mark all steps as useful (when running the second
     * algorithm in isolation).
     */
    private static final String DUPLICATE_ANALYSIS_SETUP = "~ Duplicate Analysis setup";

    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(DependencyAnalyzer.class);
    /**
     * Whether this analyzer should perform the dependency analysis.
     */
    private final boolean doDependencyAnalysis;
    /**
     * Whether this analyzer should de-duplicate rule applications.
     */
    private final boolean doDeduplicateRuleApps;

    /**
     * The proof to analyze.
     */
    private final Proof proof;
    /**
     * The dependency graph of the proof to analyze.
     */
    private final DependencyGraph graph;
    /**
     * The set of steps to keep in the proof slice.
     */
    private final Set<Node> usefulSteps = new HashSet<>();
    /**
     * The set of graph nodes required to perform the useful steps.
     * May contain more formulas than actually required after branching proof steps are
     * analyzed (i.e., it may contain graph nodes in branches listed in uselessBranches).
     */
    private final Set<GraphNode> usefulFormulas = new HashSet<>();
    /**
     * Some of the branches that will not be present in the proof slice.
     */
    private final Set<BranchLocation> uselessBranches = new HashSet<>();
    /**
     * Branch stacks, as determined by the rule application de-duplication algorithm.
     * For each proof node x, stores the nodes that have to be performed before x is
     * applied in the proof reordering.
     */
    private final Map<Node, List<Node>> branchStacks = new HashMap<>();
    /**
     * Tracker of execution time.
     */
    private final ExecutionTime executionTime = new ExecutionTime();
    /**
     * Whether any pair of rule applications was merged.
     */
    private boolean mergedAnything = false;

    /**
     * Construct and configure a new dependency analyzer.
     * At least one analysis algorithm needs to be activated.
     *
     * @param proof the proof to analyze
     * @param graph the dependency graph of that proof
     * @param doDependencyAnalysis whether to perform dependency analysis
     * @param doDeduplicateRuleApps whether to de-duplicate rule applications
     */
    public DependencyAnalyzer(
            Proof proof,
            DependencyGraph graph,
            boolean doDependencyAnalysis,
            boolean doDeduplicateRuleApps) {
        if (!doDependencyAnalysis && !doDeduplicateRuleApps) {
            throw new IllegalArgumentException("analyzer needs at least one activated algorithm");
        }
        if (proof == null) {
            throw new IllegalArgumentException("cannot analyze null proof");
        }
        this.proof = proof;
        this.graph = graph;
        this.doDependencyAnalysis = doDependencyAnalysis;
        this.doDeduplicateRuleApps = doDeduplicateRuleApps;
    }

    /**
     * Analyze the proof using the configured algorithms.
     *
     * @return analysis results
     */
    public AnalysisResults analyze() {
        if (GeneralSettings.noPruningClosed) {
            throw new IllegalStateException("cannot analyze proof with no (recorded) closed goals, "
                + "try disabling GeneralSettings.noPruningClosed");
        }
        // first check that all goals are closed without proof caching references
        if (!proof.closedGoals().stream()
                .allMatch(goal -> goal.node().lookup(ClosedBy.class) == null)) {
            throw new IllegalStateException("cannot analyze proof with cached references");
        }

        executionTime.start(TOTAL_WORK);
        proof.setStepIndices();

        if (doDependencyAnalysis) {
            executionTime.start(DEPENDENCY_ANALYSIS);
            analyzeDependencies();
            executionTime.stop(DEPENDENCY_ANALYSIS);
        }

        if (!doDependencyAnalysis && doDeduplicateRuleApps) {
            executionTime.start(DUPLICATE_ANALYSIS_SETUP);
            // mark everything as 'useful' to evaluate the second algorithm in isolation
            proof.breadthFirstSearch(proof.root(), ((proof1, visitedNode) -> {
                if (visitedNode.getAppliedRuleApp() == null) {
                    if (!visitedNode.isClosed()) {
                        usefulSteps.add(visitedNode);
                    }
                    return;
                }
                usefulSteps.add(visitedNode);
                DependencyNodeData data = visitedNode.lookup(DependencyNodeData.class);
                if (data == null) {
                    return;
                }
                data.inputs.stream().map(it -> it.first).forEach(usefulFormulas::add);
                usefulFormulas.addAll(data.outputs);
            }));
            executionTime.stop(DUPLICATE_ANALYSIS_SETUP);
        }

        if (doDeduplicateRuleApps) {
            executionTime.start(DUPLICATE_ANALYSIS);
            deduplicateRuleApps();
            executionTime.stop(DUPLICATE_ANALYSIS);
        }


        // mark each useless proof step to allow easy identification by the user
        markUselessProofSteps();

        executionTime.start(STATISTICS);
        int steps = proof.countNodes() - proof.closedGoals().size()
                + (int) proof.closedGoals()
                        .stream().filter(it -> it.node().getAppliedRuleApp() instanceof SMTRuleApp)
                        .count();
        // gather statistics on useful/useless rules
        RuleStatistics rules = getRuleStatistics();
        executionTime.stop(STATISTICS);
        executionTime.stop(TOTAL_WORK);

        return new AnalysisResults(
            proof, steps, rules, usefulSteps, usefulFormulas, uselessBranches,
            branchStacks, doDependencyAnalysis, doDeduplicateRuleApps, executionTime);
    }

    /**
     * Mark useless proof steps ({@link NodeInfo#isUselessApplication()}) based
     * on whether they are contained in {@link #usefulSteps}.
     */
    private void markUselessProofSteps() {
        Queue<Node> queue = new ArrayDeque<>();
        queue.add(proof.root());
        while (!queue.isEmpty()) {
            Node node = queue.poll();
            node.getNodeInfo().setUselessApplication(!usefulSteps.contains(node));
            node.childrenIterator().forEachRemaining(queue::add);
        }
    }

    private RuleStatistics getRuleStatistics() {
        RuleStatistics rules = new RuleStatistics();
        proof.breadthFirstSearch(proof.root(), (theProof, node) -> {
            if (node.getAppliedRuleApp() == null) {
                return;
            }
            boolean branches = node.childrenCount() > 1;
            Rule rule = node.getAppliedRuleApp().rule();
            if (usefulSteps.contains(node)) {
                rules.addApplication(rule, branches);
            } else {
                if (node.lookup(DependencyNodeData.class).inputs.stream().map(it -> it.first)
                        .anyMatch(usefulFormulas::contains)) {
                    rules.addInitialUselessApplication(rule, branches);
                } else {
                    rules.addUselessApplication(rule, branches);
                }
            }
        });
        return rules;
    }

    private void analyzeDependencies() {
        // BFS, starting from all closed goals
        Deque<Node> queue = analyzeDependenciesUsefulRoots();

        executionTime.start(DEPENDENCY_ANALYSIS2);
        while (!queue.isEmpty()) {
            Node node = queue.pop();
            // handle State Merging by throwing an error
            if (node.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                    || node.getAppliedRuleApp() instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                throw new IllegalStateException("tried to analyze proof featuring state merging!");
            }

            // closed goal & has previous step
            // => mark output (closed goal) of parent node as useful
            boolean considerOutputs = false;
            if (node.getAppliedRuleApp() == null && node.parent() != null) {
                node = node.parent();
                considerOutputs = true;
            }
            if (usefulSteps.contains(node)) {
                continue;
            }
            usefulSteps.add(node);
            DependencyNodeData data = node.lookup(DependencyNodeData.class);
            data.inputs.forEach(it -> usefulFormulas.add(it.first));

            for (Pair<GraphNode, Boolean> in : data.inputs) {
                Node thisProofStep = node;
                graph
                        .incomingEdgesOf(in.first)
                        // we don't care about steps done to derive the same formula again!
                        .filter(step -> step.getStepIndex() < thisProofStep.getStepIndex())
                        .forEach(queue::add);
            }
            if (considerOutputs) {
                data.outputs.stream().filter(ClosedGoal.class::isInstance)
                        .forEach(usefulFormulas::add);
            }
        }
        executionTime.stop(DEPENDENCY_ANALYSIS2);

        executionTime.start(DEPENDENCY_ANALYSIS3);
        analyzeDependenciesBranches();
        executionTime.stop(DEPENDENCY_ANALYSIS3);

        // unmark all 'useful' steps in useless branches
        executionTime.start(DEPENDENCY_ANALYSIS4);
        proof.breadthFirstSearch(proof.root(), (proof1, node) -> {
            if (!usefulSteps.contains(node)) {
                return;
            }
            for (BranchLocation prefix : uselessBranches) {
                if (node.getBranchLocation().hasPrefix(prefix)) {
                    usefulSteps.remove(node);
                    node.getNodeInfo().setUselessApplication(true);
                    return;
                }
            }
        });
        executionTime.stop(DEPENDENCY_ANALYSIS4);
    }

    /**
     * Calculate the set of root graph nodes that are definitely useful.
     * Includes the set of closed goals and for each open goal the formulas available
     * in that branch of the proof.
     *
     * @return queue of closed goals in the proof
     */
    private Deque<Node> analyzeDependenciesUsefulRoots() {
        Deque<Node> queue = new ArrayDeque<>();
        for (Goal e : proof.closedGoals()) {
            queue.add(e.node());
        }
        // for each open goals, get the sequent at that point in the proof
        for (Goal goal : proof.openGoals()) {
            usefulSteps.add(goal.node());
            // mark all available formulas as useful
            Sequent seq = goal.sequent();
            for (int i = 1; i <= seq.size(); i++) {
                PosInOccurrence pio =
                    PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel());
                GraphNode node = graph.getGraphNode(proof, goal.node().getBranchLocation(), pio);
                usefulFormulas.add(node);
                graph.incomingEdgesOf(node).forEach(queue::add);
            }
        }
        return queue;
    }

    /**
     * Analyze branching proof steps: they are only useful if some of their outputs are used
     * in each created branch. If some branch doesn't require the formulas added by the proof step,
     * we can use this branch to close the proof whilst omitting the branching proof step.
     */
    private void analyzeDependenciesBranches() {
        // analyze branching proof steps: they are only useful if all of their outputs were used
        proof.breadthFirstSearch(proof.root(), (proof1, node) -> {
            if (node.childrenCount() <= 1) {
                return;
            }
            DependencyNodeData data = node.lookup(DependencyNodeData.class);
            Map<BranchLocation, Collection<GraphNode>> groupedOutputs = new HashMap<>();
            node.childrenIterator().forEachRemaining(
                x -> groupedOutputs.put(x.getBranchLocation(), new ArrayList<>()));
            data.outputs.forEach(n -> groupedOutputs.get(n.getBranchLocation()).add(n));
            boolean cutWasUseful = groupedOutputs.values().stream()
                    .allMatch(l -> l.stream().anyMatch(usefulFormulas::contains));
            if (cutWasUseful) {
                return;
            }
            usefulSteps.remove(node);
            // mark sub-proof as useless, if necessary
            Set<BranchLocation> branchesToSkip = data.outputs.stream()
                    .filter(usefulFormulas::contains)
                    .map(GraphNode::getBranchLocation)
                    .collect(Collectors.toSet());
            boolean keptSomeBranch = false;
            for (int i = 0; i < node.childrenCount(); i++) {
                Node branch = node.child(i);
                // need to keep exactly one branch
                // keep any, we expect them to be roughly equivalent?
                if (!keptSomeBranch && !branchesToSkip.contains(branch.getBranchLocation())) {
                    keptSomeBranch = true;
                    continue;
                }
                uselessBranches.add(branch.getBranchLocation());
            }
            if (!keptSomeBranch) {
                throw new IllegalStateException(
                    "dependency analyzer failed to analyze branching proof step!");
            }
        });
    }

    private void deduplicateRuleApps() {
        boolean shouldExitAfterFirstMerge =
            !SlicingSettingsProvider.getSlicingSettings().getAggressiveDeduplicate(proof);

        // set of nodes placed at another position in the proof slice
        // (= added to some branch stack)
        Set<Integer> alreadyRebasedSerialNrs = new HashSet<>();
        // set of nodes merged into another node
        Set<Integer> alreadyMergedSerialNrs = new HashSet<>();

        // search for duplicate rule applications
        graph.nodes().forEach(node -> {
            if (mergedAnything) {
                return;
            }
            // groups proof steps that act upon this graph node by their rule app
            // (for obvious reasons, we don't care about origin labels here -> wrapper)
            Map<EqualsModProofIrrelevancyWrapper<RuleApp>, Set<Node>> foundDupes = new HashMap<>();
            graph.outgoingGraphEdgesOf(node).forEach(t -> {
                Node proofNode = t.first;

                // this analysis algorithm does not support proofs with State Merging
                if (proofNode.getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                        || proofNode
                                .getAppliedRuleApp() instanceof CloseAfterMergeRuleBuiltInRuleApp) {
                    throw new IllegalStateException(
                        "tried to analyze proof featuring state merging!");
                }

                // do not deduplicate branching steps
                if (proofNode.childrenCount() > 1) {
                    return;
                }
                // In combination with the dependency analysis algorithm:
                // only deduplicate useful steps
                if (!usefulSteps.contains(proofNode)) {
                    return;
                }
                // Only try to deduplicate the addition of new formulas.
                // It is unlikely that two closed goals are derived using the same formula.
                GraphNode produced = t.second;
                if (!(produced instanceof TrackedFormula)) {
                    return;
                }
                foundDupes
                        .computeIfAbsent(
                            new EqualsModProofIrrelevancyWrapper<>(proofNode.getAppliedRuleApp()),
                            _a -> new LinkedHashSet<>())
                        .add(t.third.getProofStep());
            });

            // scan dupes, try to find a set of mergable rule applications
            for (Map.Entry<EqualsModProofIrrelevancyWrapper<RuleApp>, Set<Node>> entry : foundDupes
                    .entrySet()) {
                if (mergedAnything) {
                    continue;
                }
                List<Node> steps = new ArrayList<>(entry.getValue());
                if (steps.size() <= 1) {
                    continue;
                }
                // try merging "adjacent" rule apps
                // (rule apps are sorted by step index = linear location in the proof tree)
                steps.sort(Comparator.comparing(Node::getStepIndex));
                LOGGER.trace("input {} found duplicate; attempt to merge:",
                    node.toString(false, false));

                List<Node> apps = new ArrayList<>(steps);
                List<BranchLocation> locs = apps.stream()
                        .map(Node::getBranchLocation)
                        .collect(Collectors.toList());
                for (int idxA = 0; idxA < apps.size() - 1; idxA++) {
                    if (mergedAnything) {
                        continue;
                    }
                    Node stepA = apps.get(idxA);
                    if (stepA == null) {
                        continue;
                    }
                    for (int idxB = idxA + 1; idxB < apps.size(); idxB++) {
                        if (mergedAnything) {
                            continue;
                        }
                        Node stepB = apps.get(idxB);
                        if (stepB == null) {
                            continue;
                        }
                        // To combine step A and step B, the same rule must be applied
                        // earlier in the proof. This new location (the "merge base") is simply the
                        // longest common prefix of the tw steps' branch locations.
                        // More precisely, it needs to be performed just before this branch
                        // of the proof is further split up.

                        // Check whether step A and B may be combined:
                        // 1) Verify that each graph node required by step A / step B
                        // is available at the merge base.
                        // 2) Combined proof step at the merge base does not remove
                        // any sequent formulas required by later proof steps.
                        // 3) Check that the merge is valid in the sense that the outputs of
                        // the merged proof step will be available for their intended use.

                        // Condition 3) is tested in deduplicateChecksMergabilityCorrectly
                        // (see for an example proof where two steps (11,17) may not be merged)

                        if (alreadyMergedSerialNrs.contains(stepA.serialNr())
                                || (idxA == idxB - 1
                                        && alreadyRebasedSerialNrs.contains(stepA.serialNr()))) {
                            continue;
                        }
                        // can't merge/rebase a step twice!
                        if (alreadyMergedSerialNrs.contains(stepB.serialNr())
                                || alreadyRebasedSerialNrs.contains(stepB.serialNr())) {
                            continue;
                        }
                        LOGGER.trace("considering {} {}", stepA.serialNr(), stepB.serialNr());
                        BranchLocation locA = locs.get(idxA);
                        BranchLocation locB = locs.get(idxB);
                        if (locA.equals(locB)) {
                            // skip duplicates in the same branch...
                            continue;
                        }
                        BranchLocation mergeBase = BranchLocation.commonPrefix(locA, locB);
                        boolean canMerge =
                            canMergeStepsInto(apps, idxA, stepA, stepB, locA, locB, mergeBase);
                        if (canMerge) {
                            // merge step B into step A
                            LOGGER.trace("merging {} and {}", stepA.serialNr(), stepB.serialNr());
                            locs.set(idxA, mergeBase);
                            alreadyRebasedSerialNrs.add(stepA.serialNr());
                            apps.set(idxB, null);
                            alreadyMergedSerialNrs.add(stepB.serialNr());
                            mergedAnything = shouldExitAfterFirstMerge;
                        }
                    }
                }
                // mark merged steps as useless, add one of them to the relevant branch stack
                // so that it is moved by the SlicingProofReplayer
                for (int i = 0; i < apps.size(); i++) {
                    boolean keep = apps.get(i) != null;
                    BranchLocation originalLoc = steps.get(i).getBranchLocation();
                    if (keep && !locs.get(i).equals(originalLoc)) {
                        BranchLocation differingSuffix = originalLoc.stripPrefix(locs.get(i));
                        LOGGER.trace("should be done before branching node {}", differingSuffix);
                        branchStacks.computeIfAbsent(
                            differingSuffix.getNode(0),
                            _node -> new ArrayList<>())
                                .add(steps.get(i));
                    }
                    if (!keep) {
                        usefulSteps.remove(steps.get(i));
                    }
                }
            }
        });
    }

    /**
     * Checks whether the two provided nodes can be merged into a single node.
     *
     * @param apps list of all similar rule applications
     * @param idxA index of first node in <code>apps</code>
     * @param stepA first node
     * @param stepB second node
     * @param locA branch location of first node
     * @param locB branch location of second node
     * @param mergeBase common prefix of <code>locA</code> and <code>locB</code>
     * @return whether a merge is valid
     */
    private boolean canMergeStepsInto(List<Node> apps, int idxA, Node stepA, Node stepB,
            BranchLocation locA, BranchLocation locB, BranchLocation mergeBase) {
        // calculate the step index of the merged rule application
        BranchLocation differingSuffix = locA.size() == mergeBase.size() ? locB : locA;
        int newStepIdx = differingSuffix.stripPrefix(mergeBase).getNode(0).getStepIndex() - 1;
        // verify that *all* inputs are present at the merge base
        // (see condition 1 above)
        if (!Stream.concat(
            graph.inputsOf(stepA), graph.inputsOf(stepB)).allMatch(
                graphNode -> mergeBase.hasPrefix(graphNode.getBranchLocation()))) {
            return false;
        }
        // verify that they actually use the same inputs...
        Set<GraphNode> inputsA = graph.inputsOf(stepA).collect(Collectors.toSet());
        Set<GraphNode> inputsB = graph.inputsOf(stepB).collect(Collectors.toSet());
        if (!(inputsA.containsAll(inputsB) && inputsB.containsAll(inputsA))) {
            return false;
        }
        // search for conflicting rule apps
        // (only relevant if the rule apps consume the input)
        // (see condition 2 above)
        if (otherStepsRequireConsumedInputs(apps, idxA, stepA, stepB, mergeBase)) {
            return false;
        }
        // search for conflicts concerning multiple derivations of the same formula in a branch
        // (see condition 3 above)
        return !mergeWouldBreakOtherSteps(stepA, stepB, newStepIdx);
    }

    /**
     * Checks whether a merge of <code>stepA</code> and <code>stepB</code> into a single step
     * (with step index <code>newStepIdx</code>) would make some other proof steps impossible.
     * This method only checks that the new formulas introduced by the merged step are available
     * for the further proof steps that require them.
     *
     * @param stepA first proof step
     * @param stepB second proof step
     * @param newStepIdx step index of the potential merged step
     * @return whether the merge is obstructed
     */
    private boolean mergeWouldBreakOtherSteps(Node stepA, Node stepB, int newStepIdx) {
        AtomicBoolean hasConflictOut = new AtomicBoolean(false);
        for (Node stepAB : new Node[] { stepA, stepB }) {
            // verify for each branch that the produced formula is still available at each step
            graph.outputsOf(stepAB).forEach(graphNode -> {
                // get all equivalent graph nodes in this branch
                Collection<GraphNode> allNodes = graph.nodeAndPreviousDerivations(graphNode);
                // get all steps that produce these / consume these
                Stream<AnnotatedEdge> producers = allNodes.stream()
                        .flatMap(graph::edgesProducing);
                Stream<AnnotatedEdge> consumers = allNodes.stream()
                        .flatMap(graph::edgesConsuming)
                        .filter(x -> stepAB.getBranchLocation()
                                .hasPrefix(
                                    x.getProofStep().getBranchLocation()));
                Optional<AnnotatedEdge> lastConsumer = allNodes.stream()
                        .flatMap(graph::edgesConsuming)
                        .filter(edge -> !stepAB.getBranchLocation()
                                .hasPrefix(
                                    edge.getProofStep().getBranchLocation())
                                && edge.getProofStep().getStepIndex() > stepAB
                                        .getStepIndex()
                                && edge.getProofStep().getBranchLocation()
                                        .hasPrefix(stepAB.getBranchLocation()))
                        .findFirst();
                if (lastConsumer.isPresent()) {
                    consumers = Stream.concat(consumers, Stream.of(lastConsumer.get()));
                }
                // list of (step index, produces / consumes)
                Comparator<Pair<Integer, Boolean>> byStepIndex =
                    Comparator.comparingInt(x -> x.first);
                List<Pair<Integer, Boolean>> list = Stream.concat(
                    producers.map(x -> new Pair<>(x.getProofStep().getStepIndex(), true)),
                    consumers
                            .map(x -> new Pair<>(x.getProofStep().getStepIndex(), false)))
                        .distinct()
                        .sorted(byStepIndex)
                        .collect(Collectors.toList());
                // verify that the list satisfies the correctness criteria
                Predicate<List<Pair<Integer, Boolean>>> isCorrect = l -> {
                    // the list is correct if there is at least one "produce" entry
                    // before each "consume" entry
                    boolean formulaAvailable = false;
                    for (Pair<Integer, Boolean> pair : l) {
                        if (pair.second) {
                            formulaAvailable = true;
                        } else if (!formulaAvailable) {
                            return false;
                        } else {
                            formulaAvailable = false;
                        }
                    }
                    return true;
                };
                // quick sanity check that the original proof has a valid list
                if (!isCorrect.test(list)) {
                    throw new IllegalStateException(
                        "analyzer failed to gather correct proof step list");
                }
                // reorder one proof step to simulate the merged proof
                list.remove(new Pair<>(stepAB.getStepIndex(), true));
                list.add(new Pair<>(newStepIdx, true));
                list.sort(byStepIndex);
                // if the new list is not correct: merge would break one of the listed steps
                if (!isCorrect.test(list)) {
                    hasConflictOut.set(true);
                }
            });
        }
        return hasConflictOut.get();
    }

    /**
     * Checks whether any proof steps use an input formula consumed by <code>stepA</code> or
     * <code>stepB</code>. In that case, the two steps may not be merged.
     *
     * @param apps list of all similar apps
     * @param idxA index of stepA
     * @param stepA first proof step
     * @param stepB second proof step
     * @param mergeBase merge base of stepA and stepB
     * @return whether the merge is obstructed
     */
    private boolean otherStepsRequireConsumedInputs(List<Node> apps, int idxA, Node stepA,
            Node stepB, BranchLocation mergeBase) {
        boolean consumesInput = graph.edgesOf(apps.get(idxA)).stream()
                .anyMatch(AnnotatedEdge::replacesInputNode);
        if (consumesInput) {
            // are any of the inputs used by any other edge?
            return Stream.concat(graph.inputsConsumedBy(stepA), graph.inputsConsumedBy(stepB))
                    .anyMatch(graphNode -> graph
                            .edgesUsing(graphNode)
                            // TODO: does this filter ever return false?
                            .filter(edgeX -> edgeX.getProofStep().getBranchLocation()
                                    .hasPrefix(mergeBase))
                            .anyMatch(edgeX -> edgeX.getProofStep() != stepA
                                    && edgeX.getProofStep() != stepB));
        }
        return false;
    }
}
