package consistencyChecking.dependency;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.Modality;

public class DependencyNode {

	private String myName;
	private Modality myModality;
	private Set<DependencyNode> myDependencies;

	public DependencyNode(String name, Modality modality, Set<DependencyNode> dependencies) {
		myName = name;
		myModality = modality;
		myDependencies = dependencies;
	}

	public DependencyNode(String name, Modality modality) {
		this(name, modality, new HashSet<>());
	}

	public void addDependency(DependencyNode node) {
		myDependencies.add(node);
	}

	public String getName() {
		return myName;
	}

	public Modality getModality() {
		return myModality;
	}

	public Set<DependencyNode> getDependencies() {
		return myDependencies;
	}

	// adapted from the classes: UseOperationContractRule and ProofCorrectnessMgt
	public boolean isLegal() {
		if (myModality == Modality.BOX) {
			return true;
		}
		for (DependencyNode currentNode : myDependencies) {
			// TODO: implement according to UseOperationContractRule and ProofCorrectnessMgt
		}
		return true;
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof DependencyNode) {
			DependencyNode node = (DependencyNode) o;
			if (node.myName.equals(myName)) {
				if (node.myModality == myModality) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public String toString() {
		String result = "";
		result = result + myName + " " + myModality + " (";
		for (DependencyNode currentDependency : myDependencies) {
			result = result + currentDependency.myName + "," + currentDependency.myModality + " ";
		}
		result = result + ")";
		return result;
	}

}
