package consistencyChecking.dependency;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class DependencyNode {

	private FunctionalOperationContract myContract;
	private Set<FunctionalOperationContract> myDependencies;

	private status myStatus;

	// TODO: check if these are all problems that can arise
	// and track details about the respective errors for outputting
	public enum status {
		UNKNOWN, CORRECT, MISSING_PROOFS, ILLEGAL_CYCLES
	}

	public DependencyNode(FunctionalOperationContract contract, Set<FunctionalOperationContract> dependencies) {
		myContract = contract;
		myDependencies = dependencies;
		myStatus = status.UNKNOWN;
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
		for (FunctionalOperationContract currentDependency : myDependencies) {
			if (currentDependency == null) {
				myStatus = status.MISSING_PROOFS;
				return false;
			}
		}
		if (myContract.getModality() == Modality.BOX) {
			myStatus = status.CORRECT;
			return true;
		}
		for (FunctionalOperationContract currentDepencyContract : myDependencies) {
			// TODO: implement ProofCorrectnessMgt.isContractApplicable() here
			if (!isApplicable(currentDepencyContract)) {
				myStatus = status.ILLEGAL_CYCLES;
				return false;
			}
		}
		myStatus = status.CORRECT;
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
			if (!first)
				result = result + " ";
			result = result + currentDependency.getBaseName();
			first = false;
		}
		result = result + ")";
		return result;
	}

	public boolean isApplicable(Contract contract) {
		SpecificationRepository specRepos = null;
		// get initial contracts
		ImmutableSet<Contract> contractsToBeApplied = specRepos.splitContract(contract);
		assert contractsToBeApplied != null;
		contractsToBeApplied = specRepos.getInheritedContracts(contractsToBeApplied);

		// initial paths
		ImmutableSet<ImmutableList<Contract>> newPaths = DefaultImmutableSet.nil();
		for (Contract c : contractsToBeApplied) {
			newPaths = newPaths.add(ImmutableSLList.<Contract>nil().prepend(c));
		}

		// look for cycles
		while (!newPaths.isEmpty()) {
			final Iterator<ImmutableList<Contract>> it = newPaths.iterator();
			newPaths = DefaultImmutableSet.<ImmutableList<Contract>>nil();

			while (it.hasNext()) {
				final ImmutableList<Contract> path = it.next();
				final Contract end = path.head();
				if (end.equals(myContract)) {
					if (!allHaveMeasuredBy(path.prepend(myContract))) {
						return false;
					}
				} else {
					final ImmutableSet<Proof> proofsForEnd = specRepos.getProofs(end);
					for (Proof proofForEnd : proofsForEnd) {
						final ImmutableSet<Contract> contractsUsedForEnd = proofForEnd.mgt().getUsedContracts();
						for (Contract contractUsedForEnd : contractsUsedForEnd) {
							if (!path.contains(contractUsedForEnd)) {
								final ImmutableList<Contract> extendedPath = path.prepend(contractUsedForEnd);
								newPaths = newPaths.add(extendedPath);
							}
						}
					}
				}
			}
		}

		return true;
	}
	private boolean allHaveMeasuredBy(ImmutableList<Contract> contracts) {
		for(Contract currentContract : contracts) {
		    if(!currentContract.hasMby()) {
		    	return false;
		    }
		}
		return true;
	}

}
