/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.speclang.Contract;

import org.key_project.proofmanagement.io.Logger;

import static org.key_project.proofmanagement.check.dependency.DependencyGraph.EdgeType.TERMINATION_SENSITIVE;

/**
 * Represents a node in the graph of dependencies between proofs/contracts.
 * Use {@link DependencyGraphBuilder#buildGraph(List, Logger)} to build a graph.
 *
 * @author Wolfram Pfeifer
 */
public class DependencyNode {
    /** the contract represented by this node */
    private final Contract contract;

    /**
     * Stores the outgoing edges of the node, i.e. target node and edge type
     * (if edge is termination sensitive or not). The edge type is determined by the type of
     * the contract (operation contract, dependency contract, model method axiom) and if it was
     * applied under a box or diamond modality. If the same contract is applied under different
     * modalities, only the strongest one (that one with termination, i.e. diamond)
     * is stored.
     */
    private final Map<DependencyNode, DependencyGraph.EdgeType> dependencies = new HashMap<>();

    /** indicates if the node is on stack for Tarjan's algorithm */
    private boolean onStack = false;

    /** index of the node in Tarjan's algorithm */
    private int index = -1;

    /** id of the SCC the node belongs to (for Tarjan's algorithm) */
    private int lowLink = 0;

    /**
     * Creates a new dependency node for the given contract.
     *
     * @param contract the contract represented by this node
     */
    public DependencyNode(Contract contract) {
        this.contract = contract;
    }

    boolean isOnStack() {
        return onStack;
    }

    void setOnStack(boolean onStack) {
        this.onStack = onStack;
    }

    int getIndex() {
        return index;
    }

    void setIndex(int index) {
        this.index = index;
    }

    int getLowLink() {
        return lowLink;
    }

    void setLowLink(int lowLink) {
        this.lowLink = lowLink;
    }

    public Contract getContract() {
        return contract;
    }

    public Map<DependencyNode, DependencyGraph.EdgeType> getDependencies() {
        return dependencies;
    }

    /**
     * Filters the outgoing edges for those which are termination sensitive.
     *
     * @return all termination sensitive edges starting from this node
     */
    public Set<DependencyNode> getTermSensitiveDependencies() {
        return dependencies.keySet()
                .stream()
                .filter(n -> dependencies.get(n) == TERMINATION_SENSITIVE)
                .collect(Collectors.toSet());
    }

    /**
     * Adds a new edge from this node to the given target node.
     *
     * @param targetNode the target node of the edge
     * @param edgeType the type of the edge to add
     */
    public void addEdge(DependencyNode targetNode, DependencyGraph.EdgeType edgeType) {
        DependencyGraph.EdgeType current = dependencies.get(targetNode);
        if (current != null) {
            // overwrite current edge type only if the given one is stronger
            if (current != TERMINATION_SENSITIVE) {
                dependencies.put(targetNode, edgeType);
            }
        } else {
            dependencies.put(targetNode, edgeType);
        }
    }

    // TODO: equals and hashCode needed for HashMaps?
    // @Override
    // public boolean equals(Object o) {
    // if (o instanceof DependencyNode) {
    // DependencyNode node = (DependencyNode) o;
    // if (node.contract.equals(contract)) {
    // return true;
    // }
    // }
    // return false;
    // }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append(contract.getName()).append(" -> (");
        boolean first = true;
        for (DependencyNode currentNode : dependencies.keySet()) {
            if (!first) {
                result.append(" ");
            }
            result.append(currentNode.contract.getName());
            first = false;
        }
        result.append(")");
        return result.toString();
    }
}
