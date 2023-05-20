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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.proof.BranchLocation;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.graph.DependencyGraph;
import org.key_project.slicing.graph.GraphNode;

public final class ProofReorder {
    public static void reorderProof(Proof proof, DependencyGraph depGraph) {
        Deque<GraphNode> q = new ArrayDeque<>();
        var root = proof.root();
        for (int i = 1; i <= root.sequent().size(); i++) {
            var node = depGraph.getGraphNode(proof, BranchLocation.ROOT,
                PosInOccurrence.findInSequent(root.sequent(), i, PosInTerm.getTopLevel()));
            q.addLast(node);
        }
        List<Node> newOrder = new ArrayList<>();
        Set<Node> newOrderSorted = new HashSet<>();
        while (!q.isEmpty()) {
            var nextNode = q.pop();
            System.out.println("trying " + nextNode.toString(false, false));
            depGraph.outgoingEdgesOf(nextNode).forEach(node -> {
                // TODO: do this per branch
                if (node.getBranchLocation() != BranchLocation.ROOT) {
                    return;
                }

                if (newOrderSorted.contains(node)) {
                    return;
                }
                // check that all inputs are available
                if (!depGraph.inputsOf(node)
                        .allMatch(otherNode -> depGraph.edgesProducing(otherNode)
                                .allMatch(edge -> newOrderSorted.contains(edge.getProofStep())))) {
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
        // final children
        var finalChildren =
            newOrder.stream().max(Comparator.comparing(n -> n.serialNr())).get().childrenIterator();
        var finalChildrenList = new ArrayList<>();
        while (finalChildren.hasNext()) {
            finalChildrenList.add(finalChildren.next());
        }
        for (int i = 0; i < newOrder.size(); i++) {
            newOrder.get(i).removeChildren();
        }
        // done, reorder proof steps now
        Node last = null;
        for (Node next : newOrder) {
            if (last != null) {
                last.removeChildren();
                last.add(next);
            }
            last = next;
        }
        last.addAll(finalChildrenList.toArray(new Node[0]));
    }
}
