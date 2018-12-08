package consistencyChecking.dependency;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class DependencyNode {

	private FunctionalOperationContract myContract;
	private Set<FunctionalOperationContract> myDependencies;

	public DependencyNode(FunctionalOperationContract contract, Set<FunctionalOperationContract> dependencies) {
		myContract = contract;
		myDependencies = dependencies;
	}

	public DependencyNode(FunctionalOperationContract contract) {
		this(contract, new HashSet<>());
	}

	public void addDependency(FunctionalOperationContract contract) {
		myDependencies.add(contract);
	}

	public FunctionalOperationContract getContract() {
		return myContract;
	}

	public Set<FunctionalOperationContract> getDependencies() {
		return myDependencies;
	}

	// adapted from the classes: UseOperationContractRule and ProofCorrectnessMgt
	public boolean isLegal() {
		if (myContract.getModality() == Modality.BOX) {
			return true;
		}
		for (FunctionalOperationContract currentDependency : myDependencies) {
			// TODO: implement ProofCorrectnessMgt.isContractApplicable() here
		}
		return true;
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof DependencyNode) {
			DependencyNode node = (DependencyNode) o;
			if (node.myContract.equals(myContract)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String toString() {
		String result = "";
		result = result + myContract.getBaseName() + " -> (";
		boolean first = true;
		for (FunctionalOperationContract currentDependency : myDependencies) {
			if(!first) result = result + " ";
			result = result + currentDependency.getBaseName();
			first = false;
		}
		result = result + ")";
		return result;
	}

}
