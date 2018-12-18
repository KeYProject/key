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
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

public class DependencyNode {

	private SpecificationRepository mySpecRepo;
	private FunctionalOperationContract myContract;
	private ImmutableSet<DependencyNode> myDependencies;

	// TODO: check if these are all problems that can arise
	// and track details about the respective errors for outputting
	public enum Status {
		UNKNOWN, MISSING_PROOFS, MODALITY_CLASH, ILLEGAL_CYCLES, CORRECT
	}
	private Status myStatus;
	private ImmutableSet<FunctionalOperationContract> myMissingProofs                = DefaultImmutableSet.nil();
	private ImmutableSet<FunctionalOperationContract> myModalityClashes              = DefaultImmutableSet.nil();
	private ImmutableSet<ImmutableList<FunctionalOperationContract>> myIllegalCycles = DefaultImmutableSet.nil();
	
	public DependencyNode(FunctionalOperationContract contract, ImmutableSet<DependencyNode> dependencies, SpecificationRepository specRepo) {
		mySpecRepo = specRepo;
		myContract = contract;
		myDependencies = dependencies;
		myStatus = Status.UNKNOWN;
	}
	public DependencyNode(FunctionalOperationContract contract, SpecificationRepository specRepo) {
		this(contract, DefaultImmutableSet.<DependencyNode>nil(), specRepo);
	}
	
	public void addDependency(DependencyNode dependentNode) {
		myDependencies = myDependencies.add(dependentNode);		
	}
	
	public Status getStatus() {
		return myStatus;
	}
	public ImmutableSet<FunctionalOperationContract> getMissingProofs() {
		return myMissingProofs;
	}
	public ImmutableSet<FunctionalOperationContract> getModalityClashes() {
		return myModalityClashes;
	}
	public ImmutableSet<ImmutableList<FunctionalOperationContract>> getIllegalCycles() {
		return myIllegalCycles;
	}

	// adapted from the classes: UseOperationContractRule and ProofCorrectnessMgt
	public boolean isLegal() {
		// are proofs of method contracts missing that are used in the current proof?
		for (DependencyNode currentNode : myDependencies) {
			if (currentNode == null) {
				myStatus = Status.MISSING_PROOFS;
				return false;
			}
		}
		// is the current method contract concerned with termination?
		if (myContract.getModality() == Modality.DIA) {
			// are there some modalities that do not match?
			// this check should be unnecessary
			for (DependencyNode currentNode : myDependencies) {
				if(currentNode.myContract.getModality() == Modality.BOX) {
					myStatus = Status.MODALITY_CLASH;
					return false;
				}
			}
			// do the proofs form an illegal cycle?
			for (DependencyNode currentNode : myDependencies) {
				// TODO: implement ProofCorrectnessMgt.isContractApplicable() here
				if (!isApplicable(currentNode)) {
					myStatus = Status.ILLEGAL_CYCLES;
					return false;
				}
			}
		}
		myStatus = Status.CORRECT;
		return true;
	}

	public boolean isApplicable(DependencyNode node) {
		// get initial contracts
		ImmutableSet<Contract> contractsToBeApplied = mySpecRepo.splitContract(node.myContract);
		assert contractsToBeApplied != null;
		contractsToBeApplied = mySpecRepo.getInheritedContracts(contractsToBeApplied);
		assert contractsToBeApplied.size() == 1;
		// construct initial paths from initial contracts
		ImmutableSet<ImmutableList<DependencyNode>> paths = DefaultImmutableSet.nil();
		//for (Contract c : contractsToBeApplied) {
			paths = paths.add(ImmutableSLList.<DependencyNode>nil().prepend(node));
		//}
		// check for cycles
		while (!paths.isEmpty()) {
			final Iterator<ImmutableList<DependencyNode>> it = paths.iterator();
			paths = DefaultImmutableSet.<ImmutableList<DependencyNode>>nil();
			while (it.hasNext()) {
				final ImmutableList<DependencyNode> path = it.next();
				final DependencyNode end = path.head();
				if (end.equals(this)) {
					if (!allHaveMeasuredBy(path.prepend(this))) {
						return false;
					}
				} else {
					// This needs to be edited if we want to allow multiple proofs for the same contract
					//   i.e. grapped in a loop over all proofs
					ImmutableSet<DependencyNode> currentDependencies = end.myDependencies;
					for (DependencyNode currentDependency : currentDependencies) {
						if (!path.contains(currentDependency)) {
							final ImmutableList<DependencyNode> extendedPath = path.prepend(currentDependency);
							paths = paths.add(extendedPath);
						}
					}
				}
			}
		}
		return true;
	}
	private boolean allHaveMeasuredBy(ImmutableList<DependencyNode> dependencyNodes) {
		for(DependencyNode currentNode : dependencyNodes) {
		    if(!currentNode.myContract.hasMby()) {
		    	return false;
		    }
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
		result = result + myContract.getName() + " -> (";
		boolean first = true;
		for(DependencyNode currentNode : myDependencies) {
			if(!first) result = result + " ";
			result = result + currentNode.myContract.getName();
			first = false;
		}
		result = result + ")";
		return result;
	}

}
