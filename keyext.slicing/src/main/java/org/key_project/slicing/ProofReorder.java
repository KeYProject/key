package org.key_project.slicing;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;

public final class ProofReorder {
    private ProofReorder() {

    }

    public static void reorderProof(Proof proof, DependencyGraph depGraph)
            throws IOException, ProofInputException, ProblemLoaderException,
            IntermediateProofReplayer.BuiltInConstructionException {
        MainWindow.getInstance().getMediator().stopInterface(true);

        SortedMap<BranchLocation, List<Node>> steps = new TreeMap<>();

        Set<BranchLocation> done = new HashSet<>();

        Deque<Pair<BranchLocation, Node>> todo = new ArrayDeque<>();
        todo.add(new Pair<>(BranchLocation.ROOT, proof.root()));
        while (!todo.isEmpty()) {
            var t = todo.pop();
            var root = t.second;
            var loc = t.first;
            if (done.contains(loc)) {
                continue;
            }
            done.add(loc);

            Deque<GraphNode> q = new ArrayDeque<>();
            for (int i = 1; i <= root.sequent().size(); i++) {
                var node = depGraph.getGraphNode(proof, loc,
                    PosInOccurrence.findInSequent(root.sequent(), i, PosInTerm.getTopLevel()));
                q.addLast(node);
            }
            List<Node> newOrder = new ArrayList<>();
            Set<Node> newOrderSorted = new HashSet<>();
            while (!q.isEmpty()) {
                var nextNode = q.pop();
                List<Node> finalNewOrder = newOrder;
                depGraph.outgoingEdgesOf(nextNode).forEach(node -> {
                    if (!node.getBranchLocation().equals(loc)) {
                        todo.add(new Pair<>(node.getBranchLocation(), node.getFirstInBranch()));
                        return;
                    }

                    if (newOrderSorted.contains(node)) {
                        return;
                    }
                    // check that all inputs are available
                    if (!depGraph.inputsOf(node)
                            .allMatch(otherNode -> depGraph.edgesProducing(otherNode)
                                    .allMatch(edge -> newOrderSorted.contains(edge.getProofStep())
                                            || !edge.getProofStep().getBranchLocation()
                                                    .equals(loc)))) {
                        q.addLast(nextNode);
                        return;
                    }
                    // check that all consumed inputs were already used by all other steps
                    if (!depGraph.inputsConsumedBy(node)
                            .allMatch(
                                input -> depGraph.edgesUsing(input).map(AnnotatedEdge::getProofStep)
                                        .allMatch(x -> node == x || newOrderSorted.contains(x)
                                                || !x.getBranchLocation().equals(loc)))) {
                        q.addLast(nextNode);
                        return;
                    }
                    finalNewOrder.add(node);
                    newOrderSorted.add(node);

                    var outputs = depGraph.outputsOf(node).collect(Collectors.toList());
                    Collections.reverse(outputs);
                    outputs.forEach(q::addFirst);
                });
            }
            for (int i = 0; i < newOrder.size(); i++) {
                if (newOrder.get(i).childrenCount() != 1
                        || newOrder.get(i).child(0).childrenCount() == 0) {
                    var last = newOrder.remove(i);
                    newOrder.add(last);
                    break;
                }
            }
            steps.put(loc, newOrder);
        }

        ProblemLoaderControl control = new DefaultUserInterfaceControl();
        Path tmpFile = Files.createTempFile("proof", ".proof");
        proof.saveProofObligationToFile(tmpFile.toFile());

        String bootClassPath = proof.getEnv().getJavaModel().getBootClassPath();
        AbstractProblemLoader problemLoader = new SingleThreadProblemLoader(
            tmpFile.toFile(),
            proof.getEnv().getJavaModel().getClassPathEntries(),
            bootClassPath != null ? new File(bootClassPath) : null,
            null,
            proof.getEnv().getInitConfigForEnvironment().getProfile(),
            false,
            control, false, null);
        problemLoader.load();
        // Files.delete(tmpFile);
        Proof newProof = problemLoader.getProof();
        new ReorderingReplayer(proof, newProof, steps).copy();
        newProof.saveToFile(tmpFile.toFile());
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        mediator.startInterface(true);

        ProblemLoader problemLoader2 =
            mediator.getUI().getProblemLoader(tmpFile.toFile(), null, null, null, mediator);
        // user already knows about any warnings
        problemLoader2.setIgnoreWarnings(true);
        problemLoader2.runAsynchronously();
    }
}
