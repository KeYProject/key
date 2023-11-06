package org.key_project.slicing;

import java.util.*;

import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.proof.replay.AbstractProofReplayer;
import de.uka.ilkd.key.rule.OneStepSimplifier;

import org.key_project.util.collection.ImmutableList;

/**
 * Replayer that will reorder a proof based on the provided sorting of the steps.
 *
 * @author Arne Keller
 */
public class ReorderingReplayer extends AbstractProofReplayer {

    private final SortedMap<BranchLocation, List<Node>> steps;

    public ReorderingReplayer(Proof originalProof, Proof proof,
            SortedMap<BranchLocation, List<Node>> steps) {
        super(originalProof, proof);
        this.steps = steps;
    }

    public void copy()
            throws IntermediateProofReplayer.BuiltInConstructionException {
        OneStepSimplifier.refreshOSS(proof);
        Deque<Node> nodeQueue = new ArrayDeque<>();
        Deque<Goal> queue = new ArrayDeque<>();
        queue.add(proof.getOpenGoal(proof.root()));

        for (Map.Entry<BranchLocation, List<Node>> e : steps.entrySet()) {
            nodeQueue.addAll(e.getValue());
        }

        while (!nodeQueue.isEmpty()) {
            Node nextNode = nodeQueue.pop();
            Goal nextGoal = queue.pop();
            // skip nextNode if it is a closed goal
            if (nextNode.getAppliedRuleApp() == null) {
                continue;
            }
            proof.getServices().getNameRecorder().setProposals(
                nextNode.getNameRecorder().getProposals());
            ImmutableList<Goal> newGoals = reApplyRuleApp(nextNode, nextGoal);
            List<Goal> sortedGoals = newGoals.toList();
            Collections.reverse(sortedGoals);
            for (Goal g : newGoals) {
                if (g.node().isClosed()) {
                    continue;
                }
                queue.addFirst(g);
            }
        }
    }
}
