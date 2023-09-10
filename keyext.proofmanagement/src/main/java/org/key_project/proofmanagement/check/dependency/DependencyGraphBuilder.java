/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check.dependency;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.proofmanagement.check.CheckerData;
import org.key_project.proofmanagement.io.Logger;

/**
 * A builder providing a static factory method for building dependency graphs.
 *
 * @author Wolfram Pfeifer
 */
public abstract class DependencyGraphBuilder {
    /**
     * Builds a new DependencyGraph from the given proof entries.
     *
     * @param proofEntries the proof entries to build the graph from
     * @param logger the logger to print out error messages generated during graph creation
     * @return the newly created DependencyGraph
     */
    public static DependencyGraph buildGraph(List<CheckerData.ProofEntry> proofEntries,
            Logger logger) {

        DependencyGraph graph = new DependencyGraph();

        // first create the nodes of the graph (one for each loaded proof)
        for (CheckerData.ProofEntry line : proofEntries) {

            Proof proof = line.proof;
            String contractName = proof.name().toString();
            Services services = proof.getServices();
            SpecificationRepository specRepo = services.getSpecificationRepository();
            Contract contract = specRepo.getContractByName(contractName);

            // create fresh node for current contract
            DependencyNode node = new DependencyNode(contract);
            graph.addNode(node);
        }

        // add dependencies between nodes
        for (CheckerData.ProofEntry line : proofEntries) {
            // get current node and root of proof
            Proof proof = line.proof;
            DependencyNode currentNode = graph.getNodeByName(proof.name().toString());
            BranchNodeIntermediate node = line.parseResult.getParsedResult();

            // collect all contracts the current proof refers to
            Services services = proof.getServices();
            SpecificationRepository specRepo = services.getSpecificationRepository();
            ContractAppCollector collector = new ContractAppCollector(node, proof, logger);
            collector.start();
            Map<String, DependencyGraph.EdgeType> dependentContracts = collector.getResult();

            // add actual dependency edges
            for (String depName : dependentContracts.keySet()) {
                DependencyNode dependentNode = graph.getNodeByName(depName);

                // If no node for this contract exists, create one.
                // This is the case for contracts that have no proof in bundle,
                // particularly those from JavaRedux shipped with KeY.
                if (dependentNode == null) {
                    Contract contract = specRepo.getContractByName(depName);
                    dependentNode = new DependencyNode(contract);
                    graph.addNode(dependentNode);
                }

                // add edge
                currentNode.addEdge(dependentNode, dependentContracts.get(depName));
            }
        }
        return graph;
    }
}
