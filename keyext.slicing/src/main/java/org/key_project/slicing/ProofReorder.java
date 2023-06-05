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
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.*;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;

public final class ProofReorder {
    private ProofReorder() {

    }

    public static void reorderProof(Proof proof, DependencyGraph depGraph) throws IOException, ProofInputException, ProblemLoaderException, IntermediateProofReplayer.BuiltInConstructionException {
        MainWindow.getInstance().getMediator().stopInterface(true);

        SortedMap<BranchLocation, List<Node>> steps = new TreeMap<>();

        Set<BranchLocation> done = new HashSet<>();

        Deque<Pair<BranchLocation, Node>> todo = new ArrayDeque<>();
        todo.add(new Pair<>(BranchLocation.ROOT, proof.root()));
        while (!todo.isEmpty()) {
            var t = todo.pop();
            var root = t.second;
            var loc = t.first;
            System.out.println("copying " + loc);
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
                    finalNewOrder.add(node);
                    newOrderSorted.add(node);

                    var outputs = depGraph.outputsOf(node).collect(Collectors.toList());
                    Collections.reverse(outputs);
                    outputs.forEach(q::addFirst);
                });
            }
            for (int i = 0; i < newOrder.size(); i++) {
                if (newOrder.get(i).childrenCount() == 0) {
                    newOrder = newOrder.subList(0, i + 1);
                    break;
                }
            }
            steps.put(loc, newOrder);
            /*
            var firstNode = newOrder.stream().min(Comparator.comparing(Node::serialNr)).get();
            var lastNode = newOrder.stream().max(Comparator.comparing(Node::serialNr)).get();
            newOrder.remove(lastNode);
            Node closingNode = null;
            for (int i = 0; i < newOrder.size(); i++) {
                if (newOrder.get(i).childrenCount() == 0) {
                    closingNode = newOrder.get(i);
                }
                newOrder.get(i).removeChildren();
            }
            // done, reorder proof steps now
            Node last = firstNode.parent();
            for (Node next : newOrder) {
                if (last != null) {
                    if (last.childrenCount() > 1) {
                        for (int i = 0; i < last.childrenCount(); i++) {
                            if (last.child(i).getBranchLocation() == loc) {
                                last.replaceChild(i, next);
                                break;
                            }
                        }
                    } else {
                        last.removeChildren();
                        if (last == closingNode) {
                            last = null;
                            break;
                        }
                        last.add(next);
                    }
                }
                last = next;
            }
            if (last != null) {
                last.removeChildren();
                last.add(lastNode);
            }
             */
        }

        System.out.println("done!");

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
        //Files.delete(tmpFile);
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
