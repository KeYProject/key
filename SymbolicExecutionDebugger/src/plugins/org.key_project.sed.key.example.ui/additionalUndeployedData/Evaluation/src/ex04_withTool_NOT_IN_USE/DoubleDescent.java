package ex04_withTool_NOT_IN_USE;

import java.util.Random;

abstract class Tree {
	public abstract boolean hasAdjacentZeros();

	public abstract void insert(int v);
}

class Leaf extends Tree {
	public static final Leaf ONLY = new Leaf();

	private Leaf() {
	}

	public void insert(int v) {
		throw new UnsupportedOperationException("Leaf.insert");
	}

	public boolean hasAdjacentZeros() {
		return false;
	}
}

class Node extends Tree {
	public int value;
	public Tree left, right;

	public Node(int v) {
		value = v;
		left = Leaf.ONLY;
		right = Leaf.ONLY;
	}

	public void insert(int v) {
		if (value < v) {
			if (right instanceof Leaf) {
				right = new Node(v);
			} else {
				right.insert(v);
			}
		} else {
			if (left instanceof Leaf) {
				left = new Node(v);
			} else {
				left.insert(v);
			}
		}
	}

	public boolean hasAdjacentZeros() {
		return value == 0
				&& (((Node) left).value == 0 || ((Node) right).value == 0)
				|| left.hasAdjacentZeros() || right.hasAdjacentZeros();
	}
}

public class DoubleDescent {
	public static void main(String argv[]) {
		Random random = new Random();
		Tree tree = new Node(500);
		for (int i = 0; i < 4; i++) {
			tree.insert(random.nextInt());
		}
		//tree.insert(0);
		System.out.println(tree.hasAdjacentZeros());
	}
}