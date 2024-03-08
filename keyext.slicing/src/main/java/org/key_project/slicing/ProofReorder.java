/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

import org.key_project.slicing.graph.AnnotatedEdge;
import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;
import org.key_project.slicing.graph.PseudoInput;

/**
 * Proof reordering functionality.
 *
 * @author Arne Keller
 */
public final class ProofReorder {
    private ProofReorder() {

    }

    public static void reorderProof(Proof proof, DependencyGraph depGraph)
            throws IOException, ProofInputException, ProblemLoaderException,
            IntermediateProofReplayer.BuiltInConstructionException {
        depGraph.ensureProofIsTracked(proof);
        MainWindow.getInstance().getMediator().stopInterface(true);

        SortedMap<BranchLocation, List<Node>> steps = new TreeMap<>();

        Set<BranchLocation> done = new HashSet<>();

        Deque<BranchTodo> todo = new ArrayDeque<>();
        todo.add(new BranchTodo(BranchLocation.ROOT, proof.root()));
        while (!todo.isEmpty()) {
            var t = todo.pop();
            var loc = t.location;
            var root = t.rootNode;
            if (done.contains(loc)) {
                continue;
            }
            done.add(loc);
            System.out.println("doing branch " + loc);

            // q: the list of dependency graph nodes "currently available" for proof steps
            Deque<GraphNode> q = new ArrayDeque<>();
            for (int i = 1; i <= root.sequent().size(); i++) {
                var node = depGraph.getGraphNode(proof, loc,
                    PosInOccurrence.findInSequent(root.sequent(), i, PosInTerm.getTopLevel()));
                q.addLast(node);
            }
            List<Node> newOrder = new ArrayList<>();
            Set<Node> newOrderSorted = new HashSet<>();

            // First, get all nodes that do not directly connect to the dependency graph of the
            // previous branch. These are taclets that do not have any formulas as direct inputs,
            // e.g. sign_case_distinction.
            // However, if one of these nodes splits the proof, it will be done last.
            Node finalNode = null;
            Node toCheck = root;
            while (toCheck.getBranchLocation() == loc) {
                DependencyNodeData data = toCheck.lookup(DependencyNodeData.class);
                if (data == null) {
                    break; // closed goal
                }
                if (data.inputs.size() == 1 && data.inputs.get(0).first instanceof PseudoInput) {
                    if (toCheck.childrenCount() > 1) {
                        finalNode = toCheck;
                        break;
                    }
                    // Do this one first.
                    newOrder.add(toCheck);
                }
                toCheck = toCheck.child(0);
            }

            while (!q.isEmpty()) {
                var nextNode = q.pop();
                depGraph.outgoingEdgesOf(nextNode).forEach(node -> {
                    var newLoc = node.getBranchLocation();
                    if (!newLoc.equals(loc)) {
                        /*
                         * if (!todo.containsKey(newLoc) && !done.contains(newLoc)) {
                         * System.out.println("adding branch " + newLoc);
                         * todo.put(newLoc, node.getFirstInBranch());
                         * }
                         */
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
                    newOrder.add(node);
                    newOrderSorted.add(node);

                    var outputs = depGraph.outputsOf(node).collect(Collectors.toList());
                    Collections.reverse(outputs);
                    outputs.forEach(q::addFirst);
                });
            }
            // add the next branches to the queue
            for (int i = 0; i < newOrder.size(); i++) {
                if (newOrder.get(i).childrenCount() != 1
                        || newOrder.get(i).child(0).childrenCount() == 0) {
                    var last = newOrder.remove(i);
                    var c = last.childrenCount();
                    c--;
                    while (c >= 0) {
                        todo.addFirst(
                            new BranchTodo(last.child(c).getBranchLocation(), last.child(c)));
                        c--;
                    }
                    newOrder.add(last);
                    break;
                }
            }
            if (finalNode != null) {
                newOrder.add(finalNode);
            }
            steps.put(loc, newOrder);
        }

        ProblemLoaderControl control = new DefaultUserInterfaceControl();
        Path tmpFile = Files.createTempFile("proof", ".proof");
        ProofSaver.saveProofObligationToFile(tmpFile.toFile(), proof);

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
        ProofSaver.saveToFile(tmpFile.toFile(), newProof);
        KeYMediator mediator = MainWindow.getInstance().getMediator();
        mediator.startInterface(true);

        ProblemLoader problemLoader2 =
            mediator.getUI().getProblemLoader(tmpFile.toFile(), null, null, null, mediator);
        // user already knows about any warnings
        problemLoader2.setIgnoreWarnings(true);
        problemLoader2.runAsynchronously();
    }

    private record BranchTodo(BranchLocation location, Node rootNode) {
    }
}
