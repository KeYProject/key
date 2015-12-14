package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;

/**
 * Represents a branch node. Is used to create a intermediate representation of
 * a proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis, Patrick Jattke
 *
 */
public class NUIBranchNode extends NUINode {

	/**
	 * The parent node of the branch node.
	 */
	private de.uka.ilkd.key.proof.Node parent;

	/**
	 * A list of children of the branch node.
	 */
	private LinkedList<NUINode> children;

	/**
	 * Creates a new branch node.
	 * 
	 * @param parent
	 *            The related parent node of the branch node.
	 */
	public NUIBranchNode(de.uka.ilkd.key.proof.Node parent) {
		this.parent = parent;
		children = new LinkedList<NUINode>();
	}

	/**
	 * Returns the parent node of the branch node.
	 * 
	 * @return parent The parent node of the branch node.
	 */
	public de.uka.ilkd.key.proof.Node getParent() {
		return parent;
	}

	/**
	 * Sets the parent node of the branch node.
	 * 
	 * @param parent
	 *            The node to set as parent node of the branch node.
	 */
	public void setParent(de.uka.ilkd.key.proof.Node parent) {
		this.parent = parent;
	}

	/**
	 * Returns a list of children of the branch node.
	 * 
	 * @return children
	 * 			A LinkedList of the branch node's children. 
	 */
	public LinkedList<NUINode> getChildren() {
		return children;
	}

	/**
	 * Adds a new child to the list of children.
	 * 
	 * @param child
	 *            The child to add.
	 */
	public void addChild(NUINode child) {
		this.children.addLast(child);
	}
}
