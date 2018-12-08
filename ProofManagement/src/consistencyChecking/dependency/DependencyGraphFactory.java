package consistencyChecking.dependency;

import java.util.Set;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class DependencyGraphFactory {
	
	private ContractMap myContractMap;
	private ImmutableList<BranchNodeIntermediate> myRootNodes;
	private DependencyGraph myDependencyGraph = new DependencyGraph();
	
	public DependencyGraphFactory(ImmutableList<BranchNodeIntermediate> rootNodes, ContractMap contractMap) {
    	myRootNodes = rootNodes;
    	myContractMap = contractMap;
    }
	public DependencyGraphFactory(ImmutableList<BranchNodeIntermediate> rootNodes) {
		this(rootNodes, new ContractMap());
	}

	public void start() {
		for(BranchNodeIntermediate currentIntermediate : myRootNodes) {
			// TODO: we need here the string of the contract that this proof belongs to instead of null
			FunctionalOperationContract currentContract = null;
			DependencyNode currentDependencyNode = new DependencyNode(currentContract);
			// collect all contracts referenced in the proof
			ContractApplicationCollector contractApplicationCollector = new ContractApplicationCollector(currentIntermediate);
			contractApplicationCollector.start();
			Set<String> dependentContractsAsStrings = contractApplicationCollector.getResult();
			// get contract from string and add it to the dependency set
			for(String currentDependentContractString : dependentContractsAsStrings) {
				FunctionalOperationContract currentDependentContract = myContractMap.lookup(currentDependentContractString);
				currentDependencyNode.addDependency(currentDependentContract);
			}
			// add the freshly created node to the graph
			myDependencyGraph.addNode(currentDependencyNode);
		}
	}
	
	public DependencyGraph getResult() {
		return myDependencyGraph;
	}
}
