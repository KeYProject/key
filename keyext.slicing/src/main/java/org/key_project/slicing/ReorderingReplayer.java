package org.key_project.slicing;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.proof.replay.AbstractProofReplayer;
import de.uka.ilkd.key.rule.OneStepSimplifier;

import org.key_project.util.collection.ImmutableList;

public class ReorderingReplayer extends AbstractProofReplayer {

    private final SortedMap<BranchLocation, List<Node>> steps;

    public ReorderingReplayer(Proof originalProof, Proof proof, SortedMap<BranchLocation, List<Node>> steps) throws IOException, ProofInputException, ProblemLoaderException {
        super(originalProof, proof);
        this.steps = steps;
    }

    public void copy()
            throws IntermediateProofReplayer.BuiltInConstructionException {
        OneStepSimplifier.refreshOSS(proof);
        Deque<Node> nodeQueue = new ArrayDeque<>();
        Deque<Goal> queue = new ArrayDeque<>();
        queue.add(proof.getGoal(proof.root()));

        for (Map.Entry<BranchLocation, List<Node>> e : steps.entrySet()) {
            nodeQueue.addAll(e.getValue());
        }

        while (!nodeQueue.isEmpty()) {
            Node nextNode = nodeQueue.pop();
            Goal nextGoal = queue.pop();
            System.out.println("working on goal " + nextGoal.node().serialNr());
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
                //System.out.println("adding goal " + g.node().serialNr() +" to queue");
                queue.addFirst(g);
            }
        }
    }
}
