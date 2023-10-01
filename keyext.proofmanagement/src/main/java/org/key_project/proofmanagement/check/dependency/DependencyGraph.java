/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.proofmanagement.io.Logger;

/**
 * Represents a graph of dependencies between contracts/proofs, i.e. which proof depends on
 * which contracts to be proven.
 *
 * @author Wolfram Pfeifer
 */
public class DependencyGraph {
    /**
     * indicates the type of a contract application (if termination has to be considered or not)
     */
    public enum EdgeType {
        /**
         * indicates the application of either of the following:
         * <ul>
         * <li>an operation contract inside a diamond modality</li>
         * <li>a dependency contract</li>
         * <li>a model method's contract axiom</li>
         * </ul>
         */
        TERMINATION_SENSITIVE,

        /** indicates the application of an operation contract inside a box modality */
        TERMINATION_INSENSITIVE
    }

    /**
     * Represents a strongly connected component of the graph. Note that for computing SCCs of the
     * graph only <b>termination sensitive</b> edges are considered!
     */
    public static class SCC {
        /** unique id of the SCC */
        private final int id;

        /**
         * Indicates if the SCC contains illegal cycles (unsound mutual dependencies).
         * Note: Only contains meaningful value after the DependencyChecker has been run!
         */
        private boolean legal = true;

        /** nodes the SCC consists of */
        private final Set<DependencyNode> nodes = new HashSet<>();

        /**
         * Creates a new SCC with the given id.
         *
         * @param id the unique id for the new node
         */
        public SCC(int id) {
            this.id = id;
        }

        public Set<DependencyNode> getNodes() {
            return nodes;
        }

        public boolean isLegal() {
            return legal;
        }

        public void setLegal(boolean legal) {
            this.legal = legal;
        }

        public int getId() {
            return id;
        }

        /**
         * Filters the edges starting from the given node to those where the end node
         * is also inside the SCC.
         *
         * @param node the start node of the edge
         * @return all edges of node inside the SCC
         */
        public Map<DependencyNode, EdgeType> internalEdges(DependencyNode node) {
            return node.getDependencies()
                    .keySet()
                    .stream()
                    .filter(n -> getNodes().contains(n))
                    .collect(Collectors.toMap(n -> n, n -> node.getDependencies().get(n)));
        }

        @Override
        public String toString() {
            StringBuilder result = new StringBuilder("SCC #" + id + ": {" + System.lineSeparator());
            for (DependencyNode node : getNodes()) {
                result.append("    ").append(node.getContract().getName());
                result.append(System.lineSeparator());
            }
            result.append("}");
            return result.toString();
        }
    }

    /** the nodes of this graph */
    private final Set<DependencyNode> nodes = new HashSet<>();

    /** allows for lookup of nodes by contract name */
    private final Map<String, DependencyNode> name2Node = new HashMap<>();

    /**
     * Set of the strongly connected components of the graph.
     * <code>null</code> indicates that it is invalid an has to be (re-)computed by calling
     * {@link #recalculateSCCs()}.
     */
    private Set<SCC> allSCCs = null;

    /** maps each dependency node to the SCC it corresponds to */
    private final Map<DependencyNode, SCC> node2SCC = new HashMap<>();

    /** index for Tarjan's algorithm */
    private int index = 0;

    /** stack used for Tarjan's algorithm */
    private final ArrayDeque<DependencyNode> stack = new ArrayDeque<>();

    /**
     * This constructor exists only to restrict visibility.
     * Use {@link DependencyGraphBuilder#buildGraph(List, Logger)} to build a graph.
     */
    DependencyGraph() {
    }

    public Map<DependencyNode, SCC> getNode2SCC() {
        return node2SCC;
    }

    public Set<DependencyNode> getNodes() {
        return nodes;
    }

    /**
     * Adds a node to the graph if not already present. This invalidates the SCCs
     * if already computed.
     *
     * @param node the DependencyNode to add
     */
    public void addNode(DependencyNode node) {
        if (!nodes.contains(node)) {
            nodes.add(node);
            name2Node.put(node.getContract().getName(), node);
            // adding a node directly invalidates the strongly connected components,
            // since now two SCCs may be connected
            allSCCs = null;
        }
    }

    /**
     * Returns the strongly connected components of the graph (only considering termination
     * sensitive edges). Internally, the result is cached. Adding nodes via
     * {@link #addNode(DependencyNode)} invalidates the cache.
     *
     * @return all SCCs of the graph
     */
    public Set<SCC> getAllSCCs() {
        if (allSCCs == null) {
            recalculateSCCs();
        }
        return allSCCs;
    }

    /**
     * Searches for a node with the given contract name.
     *
     * @param contractName the contract name to search for (only exact matches will be found)
     * @return the DependencyNode for the given contractName or null, if none found
     */
    public DependencyNode getNodeByName(String contractName) {
        return name2Node.get(contractName);
    }

    /**
     * Calculates the strongly connected components of the graph using Tarjan's algorithm and
     * stores them in {@link #allSCCs}.
     */
    private void recalculateSCCs() {
        // ensure that everything is fresh for a new run of Tarjan's algorithm
        index = 0;
        stack.clear();
        allSCCs = new HashSet<>();
        for (DependencyNode node : nodes) {
            node.setIndex(-1);
            node.setLowLink(0);
            node.setOnStack(false);
        }

        // starting Tarjan's algorithm:
        // iterating over all nodes ensures that SCCs of separated subgraphs are found
        for (DependencyNode node : nodes) {
            if (node.getIndex() == -1) {
                calculateSCCForNode(node);
            }
        }
    }

    /**
     * Calculates the SCC of the subgraph containing the given node
     * (as well as SCCs reachable from node).
     *
     * @param node the node to start from
     */
    private void calculateSCCForNode(DependencyNode node) {
        // each SCC is identified by its first visited node (lowlink)
        // each node has a unique index

        node.setIndex(index);
        node.setLowLink(index);
        index++;
        stack.push(node);
        node.setOnStack(true);

        // calculate SCCs only from termination sensitive edges
        for (DependencyNode succ : node.getTermSensitiveDependencies()) {
            if (succ.getIndex() == -1) {
                calculateSCCForNode(succ); // DFS descend
                node.setLowLink(Math.min(node.getLowLink(), succ.getLowLink()));
            } else if (succ.isOnStack()) { // cycle?
                node.setLowLink(Math.min(node.getLowLink(), succ.getIndex()));
            }
        }

        if (node.getLowLink() == node.getIndex()) { // back to "root" of SCC? -> store SCC
            SCC scc = new SCC(allSCCs.size());
            DependencyNode w;
            do {
                w = stack.pop();
                w.setOnStack(false);
                scc.nodes.add(w);
                node2SCC.put(w, scc);
            } while (!w.equals(node));
            allSCCs.add(scc);
        }
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        for (DependencyNode currentNode : nodes) {
            result.append(currentNode).append("\n");
        }
        return result.toString();
    }
}
