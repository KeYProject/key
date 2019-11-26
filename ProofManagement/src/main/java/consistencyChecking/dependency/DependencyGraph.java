package consistencyChecking.dependency;

import java.util.HashSet;
import java.util.Set;

public class DependencyGraph {
	
	private Set<DependencyNode> myNodes;
	
	public DependencyGraph(Set<DependencyNode> nodes) {
		myNodes = nodes;
	}
	public DependencyGraph() {
		this(new HashSet<>());		
	}
	
	public void addNode(DependencyNode node) {
		myNodes.add(node);
	}
	
	public boolean isLegal() {
		for(DependencyNode currentNode : myNodes) {
			if(!currentNode.isLegal()) {
				return false;
			}
		}
		return true;
	}
	
	@Override
	public String toString() {
		String result = "";
		for(DependencyNode currentNode : myNodes) {
			result = result + currentNode + "\n";
		}
		return result;
	}
	
}
