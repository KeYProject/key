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
 *       Debug method {@link #rotateLeft(Node)} which performs a rotate left 
 *       operation on the current AVL tree
 *    </li>
 *    <li>In view 'Debug', click on 'Resume' to start symbolic execution</li>
 *    <li>Select leftmost method return node</li>
 *    <li>Click on context menu item 'Visualize Configurations'</li>
 * </ol>
 * The displayed memory configuration in the opened editor shows one possible 
 * AVL tree shape at the selected node. The slider in the bottom toolbar can be 
 * used to inspect different (non-isomorphic) shapes. In all of them can be seen 
 * that a {@link Node#parent} field points to itself, which indicates that the 
 * rotate operation invalidates the parent relationship.
 * <p> 
 * If of interest, the AVL tree shape before the method was called can be shown 
 * by selecting radio button 'Initial'.
 */
public class AVLTree {
	protected Node root;
	
	protected void rotateLeft(Node current) {
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