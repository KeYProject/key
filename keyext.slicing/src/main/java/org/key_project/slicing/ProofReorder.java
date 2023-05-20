package org.key_project.slicing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;

import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;

public final class ProofReorder {
    private ProofReorder() {

    }

    public static void reorderProof(Proof proof, DependencyGraph depGraph) {
        MainWindow.getInstance().getMediator().stopInterface(true);

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
                    newOrder.add(node);
                    newOrderSorted.add(node);

                    var outputs = depGraph.outputsOf(node).collect(Collectors.toList());
                    Collections.reverse(outputs);
                    outputs.forEach(q::addFirst);
                });
            }
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
        }

        System.out.println("done!");
        MainWindow.getInstance().getMediator().startInterface(true);
    }
}
