package org.key_project.proofmanagement.check.dependency;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Pair;

public abstract class DependencyGraphBuilder {

    public static DependencyGraph buildGraph(SpecificationRepository specRepo, List<Pair<String, BranchNodeIntermediate>> contractProofPairs) {

        // create empty graph
        DependencyGraph graph = new DependencyGraph();
        // create empty graph nodes
        Map<String, DependencyNode> dependencyNodes = new HashMap<>();

        for (Pair<String, BranchNodeIntermediate> currentContractProofPair : contractProofPairs) {
            String c = currentContractProofPair.first;

            //Contract contract = contractMap.lookup(c);
            Contract contract = specRepo.getContractByName(c);

            // create fresh node for current contract
            DependencyNode node = new DependencyNode(contract);
            // add node to graph
            dependencyNodes.put(c, node);
            // and the node map for later reference
            graph.addNode(node);
        }

        // add dependencies between nodes
        for (Pair<String, BranchNodeIntermediate> currentContractProofPair : contractProofPairs) {
            // get current node and root of proof
            DependencyNode currentDependencyNode = dependencyNodes.get(currentContractProofPair.first);
            BranchNodeIntermediate currentIntermediateNode = currentContractProofPair.second;

            // collect all contracts referenced to in current proof
            ContractApplicationCollector contractApplicationCollector = new ContractApplicationCollector(currentIntermediateNode, specRepo);
            contractApplicationCollector.start();
            Set<Pair<String, Modality>> dependentContracts = contractApplicationCollector.getResult();

            // add dependencies between nodes
            for (Pair<String, Modality> currentDependent : dependentContracts) {
                DependencyNode dependentNode = dependencyNodes.get(currentDependent.first);

                // TODO: should these missing dependency nodes be created earlier (to ensure that their dependencies
                //  are collected as well)?
                if (dependentNode == null) {
                    Contract contract = specRepo.getContractByName(currentDependent.first);
                    dependentNode = new DependencyNode(contract);
                    graph.addNode(dependentNode);
                }

                currentDependencyNode.addDependency(dependentNode, currentDependent.second);
            }
            // add the freshly created node to the graph
            graph.addNode(currentDependencyNode);
        }
        // return the created graph
        return graph;
    }

}
