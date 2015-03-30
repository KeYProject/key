package algorithm;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import algorithm.AVLTree.Node;


public class AVLTreeTest {
	@Test
	public void testPostiveNumbersInOrder() {
		List<Integer> expectedValues = new LinkedList<Integer>();
		AVLTree tree = new AVLTree();
//		assertAVLTree(tree, expectedValues);
		for (int i = 1; i <= 11; i++) {
			tree.insert(i);
			expectedValues.add(Integer.valueOf(i));
//			assertAVLTree(tree, expectedValues);
		}
//System.out.println(tree);		
		assertAVLTree(tree, expectedValues);
	}
	
//	@Test
//	public void testNegativeNumbersInOrder() {
//		List<Integer> expectedValues = new LinkedList<Integer>();
//		AVLTree tree = new AVLTree();
//		assertAVLTree(tree, expectedValues);
//		for (int i = -1; i >= -20; i--) {
//			tree.insert(i);
//			expectedValues.add(Integer.valueOf(i));
//			assertAVLTree(tree, expectedValues);
//		}
//	}

	protected static void assertAVLTree(AVLTree tree, List<Integer> expectedValues) {
		List<Integer> expectedCopy = new LinkedList<Integer>(expectedValues);
		assertNotNull(tree);
		if (tree.root != null) {
			// Compute child depth
			Map<Node, Integer> nodeChildDepths = new HashMap<Node, Integer>();
			fillChildDepthMap(tree.root, nodeChildDepths);
			// Test tree
			assertNull(tree.root.parent);
			assertAVLNode(tree.root, expectedCopy, nodeChildDepths);
		}
		assertTrue(expectedCopy.isEmpty());
	}
	
	protected static int fillChildDepthMap(Node node, Map<Node, Integer> nodeChildDepths) {
		int leftDepth = 0;
		if (node.left != null) {
			leftDepth = fillChildDepthMap(node.left, nodeChildDepths) + 1;
		}
		int rightDepth = 0;
		if (node.right != null) {
			rightDepth = fillChildDepthMap(node.right, nodeChildDepths) + 1;
		}
		int depth = leftDepth > rightDepth ? leftDepth : rightDepth;
		nodeChildDepths.put(node, Integer.valueOf(depth));
		return depth;
	}
	
	protected static void assertAVLNode(Node node, List<Integer> expectedValues, Map<Node, Integer> nodeChildDepths) {
		// Test node
		assertNotNull(node);
		assertTrue(expectedValues.remove(Integer.valueOf(node.value)));
		assertTrue(node.height >= -1);
		assertTrue(node.height <= 1);
		if (node.left != null) {
			assertTrue(node.left.value < node.value);
			assertSame("wrong parent at left child", node, node.left.parent);
		}
		if (node.right != null) {
			assertTrue(node.right.value >= node.value);
			assertSame("wrong parent at right child", node, node.right.parent);
		}
		// Test children
		if (node.left != null) {
			assertAVLNode(node.left, expectedValues, nodeChildDepths);
		}
		if (node.right != null) {
			assertAVLNode(node.right, expectedValues, nodeChildDepths);
		}
//		Integer leftDepth = nodeChildDepths.get(node.left);
//		Integer rightDepth = nodeChildDepths.get(node.right);
//		assertEquals(node.toString(), (rightDepth != null ? rightDepth.intValue() + 1 : 0) - (leftDepth != null ? leftDepth.intValue() + 1 : 0), node.height);
	}
}
