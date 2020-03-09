package org.key_project.proofmanagement.check.dependency;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class DependencyGraph {

    // IMPORTANT: do not remove -> needed for output with StringTemplate
    public Set<DependencyNode> getNodes() {
        return nodes;
    }

    private final Set<DependencyNode> nodes = new HashSet<>();

    // for Tarjan algorithm
    /** Set of all strongly connected components of the graph.
     * null indicates that it is invalid an has to be (re-)computed by calling
     * {@link #updateSCCs()}.
     * Note that the SCCs actually form a DAG.
     */
    private Set<SCC> allSCCs = new HashSet<>();
    private int index = 0;
    private final ArrayDeque<DependencyNode> stack = new ArrayDeque<>();

    /** maps each dependency node to the SCC it corresponds to */
    private Map<DependencyNode, SCC> node2SCC = new HashMap<>();

    /**
     * Represents a strongly connected component of the graph.
     */
    private static class SCC {
        /** edges to other SCCs */
        private Map<SCC, Modality> outEdges = new HashMap<>();
        /** nodes the SCC consists of */
        private Set<DependencyNode> originalNodes = new HashSet<>();
        /** the modality of the SCC, i.e. if termination of the contracts
         * has to be proved or not */
        private Modality modality;
    }

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
            node2SCC = new HashMap<>();
            stack.clear();
        }
    }

    /**
     * Checks if the graph is legal, i.e. has no unsound cyclic dependencies or modality clashes.
     * @return true iff the graph is legal
     */
    public boolean isLegal() {
        // ensure that allSCCs is up to date
        updateSCCs();
        //for (Set<DependencyNode> scc : allSCCs) {
        for (SCC scc : allSCCs) {
            // possible cases:
            // size == 1 -> no further method calls -> allowed without "measured by" clause
            // size > 1  -> at least one call (recursive or different method) -> "measured by" needed
            if (scc.originalNodes.size() > 1) {
                if (!allHaveMeasuredBy(scc)) {
                    return false;
                }
            }
            // check modalities inside each SCC
            if (!compatibleModalities(scc)) {
               return false;
            }

            // if not set (for SCCs of size 1), determine modality of SCC
            if (scc.modality == null) {
                Contract c = scc.originalNodes.iterator().next().getContract();
                if (c instanceof FunctionalOperationContract) {
                    scc.modality = ((FunctionalOperationContract) c).getModality();
                } else {
                    // fallback (e.g. for DependencyContract)
                    // -> we are not interested in termination
                    scc.modality = Modality.BOX;
                }
            }

            // check modalities between SCCs (edges of DAG of SCCs):
            // all modalities of outgoing edges of a SCC must be weaker than SCCs modality
            for (Map.Entry<SCC, Modality> next : scc.outEdges.entrySet()) {
                if (scc.modality.terminationSensitive()
                        && !next.getValue().terminationSensitive()) {
                    // TODO: set status: modality clash found
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean allHaveMeasuredBy(SCC scc) {
        for (DependencyNode node : scc.originalNodes) {
            if (node.getContract().hasMby()) {
                // TODO: set status: termination argument missing
                return false;
            }
        }
        return true;
    }

    // TODO: side effects: calculates and stores modalitiy for given SCC
    private static boolean compatibleModalities(SCC scc) {
        // determine modality of SCC and check edges inside SCC
        for (DependencyNode u : scc.originalNodes) {
            for (Map.Entry<DependencyNode, Modality> entry : u.getDependencies().entrySet()) {
                DependencyNode v = entry.getKey();

                // all edges (u, v) inside scc (includes self edges!) ...
                if (scc.originalNodes.contains(v)) {
                    // ... must have same modality
                    // TODO: box contract calls diamond should be allowed (?) ...
                    Modality m = entry.getValue();
                    if (scc.modality == null) {
                        scc.modality = m;
                    } else if (!scc.modality.equals(m)) {
                        // incompatibility of modalities found!
                        // TODO: set status: modality clash found
                        return false;
                    }
                }
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
            allSCCs = new HashSet<>();
        }
        // iterating over all nodes ensures that SCCs of separated subgraphs are found
        for (DependencyNode node : nodes) {
            if (node.index == -1) {
                calculateSCCForNode(node);
            }
        }

        // calculate edges between SCCs (looks like cubic running time, but is actually in O(E)
        // of the original graph)
        for (SCC scc : allSCCs) {
            for (DependencyNode n : scc.originalNodes) {
                for (Map.Entry<DependencyNode, Modality> e : n.getDependencies().entrySet()) {
                    SCC other = node2SCC.get(e.getKey());
                    // collect edges pointing to another SCC ...
                    if (other != scc) {
                        // ... but only update if edge is not yet present or modality is stronger
                        Modality current = scc.outEdges.get(other);
                        if (current == null ||
                                (!current.terminationSensitive()
                                    && e.getValue().terminationSensitive())) {
                            // add edge / update modality
                            scc.outEdges.put(other, e.getValue());
                        }
                    }
                }
            }
        }
    }

    /**
     * Calculates the SCC of the subgraph containing the given node
     * (as well as SCCs reachable from node).
     * @param node the node to start
     */
    private void calculateSCCForNode(DependencyNode node) {
        // each SCC is identified by its first visited node (lowlink)
        // each node has a unique index

        node.index = index;
        node.lowLink = index;
        index++;
        stack.push(node);
        node.onStack = true;

        for (DependencyNode succ : node.getDependencies().keySet()) {
            if (succ.index == -1) {
                calculateSCCForNode(succ);      // DFS descend
                node.lowLink = Math.min(node.lowLink, succ.lowLink);
            } else if (succ.onStack) {          // cycle?
                node.lowLink = Math.min(node.lowLink, succ.index);
            }
        }

        if (node.lowLink == node.index) {       // back to "root" of SCC? -> store SCC
            SCC scc = new SCC();
            DependencyNode w;
            do {
                w = stack.pop();
                w.onStack = false;
                scc.originalNodes.add(w);
                node2SCC.put(w, scc);
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
