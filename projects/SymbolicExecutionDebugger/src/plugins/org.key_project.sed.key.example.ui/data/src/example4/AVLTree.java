package example4;

/**
 * Comprehension of large data structures is difficult and finding bugs can 
 * easily become a nightmare. This is in particular true for non-trivial 
 * data-structures like balanced trees.
 * <p>
 * This example demonstrates how the symbolic memory visualization of the SED 
 * helps to efficiently find a bug in an AVL tree implementation. 
 * <ol>
 *    <li>
 *       Launch method {@link #rotateLeft(Node)} which performs a rotate left 
 *       operation on the current AVL tree.
 *    </li>
 *    <li>Resume execution.</li>
 *    <li>
 *       Visualize memory configurations of the most left method return node.
 *    </li>
 * </ol>
 * The displayed memory configuration shows one of the possible AVL tree shapes 
 * at the selected node. The slider in the bottom toolbar can be used to inspect 
 * different (non-isomorphic) shapes. In all of them can be seen that a parent 
 * field points to itself, which indicates that the rotate operation invalidates 
 * the parent relationship.
 * <p> 
 * If wanted, the AVL tree shape before the rotation can be shown by selecting 
 * radio button 'initial'.
 */
public class AVLTree {
	protected Node root;
	
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
