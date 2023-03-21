package de.uka.ilkd.key.proof.replay;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayDeque;

public class CopyingProofReplayer extends AbstractProofReplayer {
    public CopyingProofReplayer(Proof originalProof, Proof proof) {
        super(originalProof, proof);
    }

    public void copy(Node originalNode, Goal newNode)
            throws IntermediateProofReplayer.BuiltInConstructionException {
        var nodeQueue = new ArrayDeque<Node>();
        var queue = new ArrayDeque<Goal>();
        queue.add(newNode);
        nodeQueue.add(originalNode);
        while (!nodeQueue.isEmpty()) {
            Node nextNode = nodeQueue.pop();
            Goal nextGoal = queue.pop();
            for (int i = 0; i < nextNode.childrenCount(); i++) {
                nodeQueue.add(nextNode.child(i));
            }
            // skip nextNode if it is a closed goal
            if (nextNode.getAppliedRuleApp() == null) {
                queue.addFirst(nextGoal);
                continue;
            }
            ImmutableList<Goal> newGoals = reApplyRuleApp(nextNode, nextGoal);
            for (Goal g : newGoals) {
                queue.add(g);
            }
        }
    }
}
