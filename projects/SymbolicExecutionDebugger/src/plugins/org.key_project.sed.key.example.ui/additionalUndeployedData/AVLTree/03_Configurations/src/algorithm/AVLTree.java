package algorithm;

public class AVLTree {
	protected Node root;
	
	public void insert(int value) {
		if (root == null) {
			root = new Node(null, value);
		}
		else {
			insert(root, value);
		}
	}
	
	private int insert(Node parent, int value) {
		// Select left or right sub tree
		if (value < parent.value) {
			// Insert value as new node
			int newChildHeight;
			if (parent.left != null) {
				newChildHeight = insert(parent.left, value);
			}
			else {
				parent.left = new Node(parent, value);
				newChildHeight = -1;
			}
			parent.height += newChildHeight;
			// Balance sub tree
			if (parent.height == -2) {
				rotateRight(parent);
				return 0;
			}
			else {
				return -1;
			}
		}
		else {
			// Insert value as new node
			int newChildHeight;
			if (parent.right != null) {
				newChildHeight = insert(parent.right, value);
			}
			else {
				parent.right = new Node(parent, value);
				newChildHeight = 1;
			}
			// Balance sub tree
			parent.height += newChildHeight;
			if (parent.height == 2) {
				rotateLeft(parent);
				return 0;
			}
			else {
				return 1;
			}
		}
	}
	
	private void rotateLeft(Node current) {
		Node newParent = current.right;
		Node oldLeft = newParent.left;
		newParent.left = current;
		newParent.height = 0;
		current.height = 0;
		current.right = oldLeft;
		if (oldLeft != null) {
			oldLeft.parent = current.right; // Correct: oldLeft.parent = current
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
	}
	
	private void rotateRight(Node current) {
		Node newParent = current.left;
		Node oldRight = newParent.right;
		newParent.right = current;
		newParent.height = 0;
		current.height = 0;
		current.left = oldRight;
		if (oldRight != null) {
			oldRight.parent = current.left;
		}
		if (current.parent == null) {
			root = newParent;
			newParent.parent = null;
		}
		else {
			current.parent.left = newParent;
			newParent.parent = current.parent;
		}
		current.parent = newParent;
	}

	public String toString() {
		String text = "AVL Tree";
		if (root != null) {
			text += toString(0, " (root)", root);
		}
		return text;
	}
	
	public String toString(int level, String identifier, Node node) {
		String text = "\n";
		for (int i = 0; i < level; i++) {
			text += "\t";
		}
		text += node.toString();
		if (identifier != null) {
			text += identifier;
		}
		if (node.left != null) {
			text += toString(level + 1, " (left)", node.left);
		}
		if (node.right != null) {
			text += toString(level + 1, " (right)", node.right);
		}
		return text;
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
