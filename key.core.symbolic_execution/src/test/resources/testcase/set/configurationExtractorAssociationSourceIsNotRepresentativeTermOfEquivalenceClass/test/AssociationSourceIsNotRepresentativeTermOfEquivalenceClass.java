package algorithm;

public class AssociationSourceIsNotRepresentativeTermOfEquivalenceClass {
	protected Node root;
	
	// precondition: current != null && current.right != null
	private Node compute(Node current) {
		Node newParent = current.right;
		Node oldLeft = newParent.left;
		newParent.left = current;
		newParent.height = 0;
		current.height = 0;
		current.right = oldLeft;
		if (oldLeft != null) {
			oldLeft.parent = current.right; // Correct oldLeft.parent = current;
		}
		if (current.parent == null) {
			root = newParent;
			newParent.parent = null;
		}
		else {
			current.parent.right = newParent;
			newParent.parent = current.parent;
		}
		current.parent = newParent;
		return current;
	}
	

	protected static class Node {
		protected int value;
		
		protected int height;
		
		protected Node left;
		
		protected Node right;
		
		protected Node parent;

		protected Node(Node parent, int value) {
			this.value = value;
			this.parent = parent;
		}
		
		public String toString() {
			return value + " with height " + height;
		}
	}
}
