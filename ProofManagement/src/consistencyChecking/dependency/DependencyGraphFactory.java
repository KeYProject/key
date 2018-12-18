package consistencyChecking.dependency;

import java.util.Set;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.proof.io.intermediate.BranchNodeIntermediate;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.Pair;

public class DependencyGraphFactory {
	
	private ContractMap myContractMap;
	private ImmutableList<Pair<String, BranchNodeIntermediate>> myContractProofPairs;
	private DependencyGraph myDependencyGraph = new DependencyGraph();
	
	public DependencyGraphFactory(ImmutableList<Pair<String, BranchNodeIntermediate>> contractProofPairs, ContractMap contractMap) {
    	myContractProofPairs = contractProofPairs;
    	myContractMap = contractMap;
    }
	public DependencyGraphFactory(SpecificationRepository specRepo, ImmutableList<Pair<String, BranchNodeIntermediate>> contractProofPairs) {
		this(contractProofPairs, new ContractMap(specRepo));
	}

	public void start() {
		for(Pair<String,BranchNodeIntermediate> currentContractProofPair : myContractProofPairs) {
			String currentContractString = currentContractProofPair.first;
			BranchNodeIntermediate currentIntermediateNode = currentContractProofPair.second;

			// TODO: we need here the string of the contract that this proof belongs to instead of null
			FunctionalOperationContract currentContract = myContractMap.lookup(currentContractString);
			DependencyNode currentDependencyNode = new DependencyNode(currentContract);

			// collect all contracts referenced in the proof
			ContractApplicationCollector contractApplicationCollector = new ContractApplicationCollector(currentIntermediateNode);
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
