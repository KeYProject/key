package consistencyChecking.dependency;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;

public abstract class DependencyGraphBuilder {
	
	public static DependencyGraph buildGraph(SpecificationRepository specRepo, ImmutableList<Pair<String, BranchNodeIntermediate>> contractProofPairs) {
		// create contract map to lookup contracts from their strings
		ContractMap contractMap = new ContractMap(specRepo);
		// create empty graph
		DependencyGraph graph = new DependencyGraph();
		// create empty graph nodes
		Map<String,DependencyNode> dependencyNodes = new HashMap<>();
		for(Pair<String,BranchNodeIntermediate> currentContractProofPair : contractProofPairs) {
			String currentContractString = currentContractProofPair.first;
			FunctionalOperationContract currentContract = contractMap.lookup(currentContractString);
			// create fresh node for current contract
			DependencyNode currentDependencyNode = new DependencyNode(currentContract, specRepo);
			// add node to graph
			dependencyNodes.put(currentContractString, currentDependencyNode);
			// and the node map for later reference
			graph.addNode(currentDependencyNode);
		}
		// add dependencies between nodes
		for(Pair<String,BranchNodeIntermediate> currentContractProofPair : contractProofPairs) {
			// get current node and root of proof
			DependencyNode currentDependencyNode = dependencyNodes.get(currentContractProofPair.first);
			BranchNodeIntermediate currentIntermediateNode = currentContractProofPair.second;
			// collect all contracts referenced to in current proof
			ContractApplicationCollector contractApplicationCollector = new ContractApplicationCollector(currentIntermediateNode);
			contractApplicationCollector.start();
			Set<String> dependentContractsAsStrings = contractApplicationCollector.getResult();
			// add dependencies between nodes
			for(String currentDependentContractString : dependentContractsAsStrings) {
				DependencyNode dependentNode = dependencyNodes.get(currentDependentContractString);
				currentDependencyNode.addDependency(dependentNode);
			}
			// add the freshly created node to the graph
			graph.addNode(currentDependencyNode);
		}
		// return the created graph
		return graph;
	}

}
