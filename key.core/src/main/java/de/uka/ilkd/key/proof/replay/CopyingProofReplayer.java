/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.replay;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Set;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.rule.OneStepSimplifier;

import org.key_project.util.collection.ImmutableList;

/**
 * Replayer that copies proof steps from one proof to another.
 *
 * @author Arne Keller
 */
public class CopyingProofReplayer extends AbstractProofReplayer {
    /**
     * Construct a new replayer.
     *
     * @param originalProof proof to copy from
     * @param proof proof to add steps to
     */
    public CopyingProofReplayer(Proof originalProof, Proof proof) {
        super(originalProof, proof);
    }

    /**
     * Copy steps from <code>originalNode</code> to <code>newNode</code>
     *
     * @param originalNode original proof
     * @param newNode open goal in new proof
     * @param skippedNodes nodes to skip when copying
     * @throws IntermediateProofReplayer.BuiltInConstructionException on error
     */
    public void copy(Node originalNode, Goal newNode, Set<Node> skippedNodes)
            throws IntermediateProofReplayer.BuiltInConstructionException {
        newNode.proof().reOpenGoal(newNode);
        newNode.proof().register(this, CopyingProofReplayer.class);
        newNode.proof().setMutedProofCloseEvents(true);
        OneStepSimplifier.refreshOSS(newNode.proof());

        // nodeQueue: nodes in the ORIGINAL proof
        Deque<Node> nodeQueue = new ArrayDeque<>();
        // queue: nodes in the NEW proof
        Deque<Goal> queue = new ArrayDeque<>();

        queue.add(newNode);
        nodeQueue.add(originalNode);
        while (!nodeQueue.isEmpty() && !queue.isEmpty()) {
            Node nextNode = nodeQueue.pop();
            Goal nextGoal = queue.pop();
            for (int i = nextNode.childrenCount() - 1; i >= 0; i--) {
                nodeQueue.addFirst(nextNode.child(i));
            }
            // skip explicitly requested nodes
            if (skippedNodes.contains(nextNode)) {
                if (!nextGoal.node().isClosed()) {
                    queue.addFirst(nextGoal);
                }
                continue;
            }
            // skip nextNode if it is a closed goal
            if (nextNode.getAppliedRuleApp() == null) {
                continue;
            }
            ImmutableList<Goal> newGoals = reApplyRuleApp(nextNode, nextGoal);
            for (Goal g : newGoals) {
                queue.addFirst(g);
            }
        }
        newNode.proof().setMutedProofCloseEvents(false);
        newNode.proof().deregister(this, CopyingProofReplayer.class);
    }
}
