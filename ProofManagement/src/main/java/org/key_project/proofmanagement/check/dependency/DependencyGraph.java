package org.key_project.proofmanagement.check.dependency;

import de.uka.ilkd.key.logic.op.Modality;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class DependencyGraph {

    private final Set<DependencyNode> nodes = new HashSet<>();

    // for Tarjan algorithm
    /** List of all strongly connected components of the graph.
     * null indicates that it is invalid an has to be (re-)computed by calling
     * {@link #updateSCCs()}. */
    private List<List<DependencyNode>> allSCCs = null;
    private int index = 0;
    private final ArrayDeque<DependencyNode> stack = new ArrayDeque<>();

    /**
     * Adds a node to the graph if not already present. This invalidates the SCCs
     * if already computed.
     * @param node the DependencyNode to add
     */
    public void addNode(DependencyNode node) {
        if (nodes.contains(node)) {
            System.out.println("Dependency node already present: " + node);
        } else {
            nodes.add(node);
            // adding a node directly invalidates the strongly connected components,
            // since now two SCCs may be connected
            allSCCs = null;
        }
    }

    /**
     * Checks if the graph is legal, i.e. has no unsound cyclic dependencies or modality clashes.
     * @return true iff the graph is legal
     */
    public boolean isLegal() {
        // ensure that allSCCs is up to date
        updateSCCs();
        for (List<DependencyNode> scc : allSCCs) {
            // possible cases:
            // size == 1 -> no further method calls -> allowed without "measured by" clause
            // size > 1  -> at least one call (recursive or different method) -> "measured by" needed
            if (scc.size() > 1) {
                if (!allHaveMeasuredBy(scc) || !compatibleModalities(scc)) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean allHaveMeasuredBy(List<DependencyNode> scc) {
        for (DependencyNode node : scc) {
            if (node.getContract().hasMby()) {
                // TODO: set status: termination argument missing
                return false;
            }
        }
        return true;
    }

    private static boolean compatibleModalities(List<DependencyNode> scc) {
        Modality current = null;
        for (int i = 0; i < scc.size(); i++) {
            DependencyNode node = scc.get(i);
            // TODO: Next two lines fail for SCCs that are not simple cycles (cross edges!)
            DependencyNode nextInSCC = scc.get((i+1) % scc.size());
            Modality next = node.getDependencies().get(nextInSCC);
            if (current == null) {
                current = next;
            } else if (!current.equals(next)) {
                // incompatibility of modalities found!
                // TODO: set status: modality clash found
                return false;
            }
        }
        return true;
    }

    /**
     * Calculates the strongly connected components of the graph using Tarjan's algorithm and
     * stores them in {@link #allSCCs}.
     */
    private void updateSCCs() {
        if (allSCCs == null) {
            allSCCs = new ArrayList<>();
        }
        // iterating over all nodes ensures that SCCs of separated subgraphs are found
        for (DependencyNode node : nodes) {
            if (node.index == -1) {
                calculateSCCForNode(node);
            }
        }
    }

    /**
     * Calculates the SCCs of the subgraph containing the given node.
     * @param node the node to start
     */
    private void calculateSCCForNode(DependencyNode node) {
        node.index = index;
        node.lowLink = index;
        index++;
        stack.push(node);
        node.onStack = true;

        for (DependencyNode succ : node.getDependencies().keySet()) {
            if (succ.index == -1) {
                calculateSCCForNode(succ);
                node.lowLink = Math.min(node.lowLink, succ.lowLink);
            } else if (succ.onStack) {
                node.lowLink = Math.min(node.lowLink, succ.index);
            }
        }

        if (node.lowLink == node.index) {
            List<DependencyNode> scc = new ArrayList<>();
            DependencyNode w;
            do {
                w = stack.pop();
                w.onStack = false;
                scc.add(w);
            } while (!w.equals(node));
            allSCCs.add(scc);
        }
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        for(DependencyNode currentNode : nodes) {
            result.append(currentNode).append("\n");
        }
        return result.toString();
    }
}
