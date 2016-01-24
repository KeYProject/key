package de.uka.ilkd.key.nui.prooftree;

/**
 * Abstract class for representing a NUINode, which can be:
 * <ul>
 * <li>a NUIBranchNode {@link de.uka.ilkd.key.nui.prooftree.NUIBranchNode}</li>
 * <li>a NUILeafNode {@link de.uka.ilkd.key.nui.prooftree.NUILeafNode}</li>
 * <li>a NUIInnerNode {@link de.uka.ilkd.key.nui.prooftree.NUIInnerNode}</li>
 * </ul>
 * 
 * The class is used to create an intermediate graphical of the proof tree
 * consisting of objects of type {@link de.uka.ilkd.key.proof.Node}. This
 * representation only consists of information relevant to create a decorated
 * tree.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public abstract class NUINode {

	/**
	 * The node text label.
	 */
	private String label;

	/**
	 * Marks if the node has the closed property.
	 */
	private boolean closed;

	/**
	 * Marks if the node has the linked property.
	 */
	private boolean linked;

	/**
	 * Marks if the node has the interactive property.
	 */
	private boolean interactive;

	/**
	 * Marks if the node has the active property.
	 */
	private boolean active;

	/**
	 * Marks if notes for this node exist.
	 */
	private boolean hasNotes;

	/**
	 * The serial number of the proof node.
	 */
	private String serialNumber;

	/**
	 * the parent node of this node.
	 */
	private NUINode parent;

	/**
	 * Marks if the node should be highlighted e.g. in case that it is searched
	 * for.
	 */
	private boolean isHighlighted;

	/**
	 * Marks if the node is currently visible in the treeView.
	 */
	private boolean isVisible = true;

	/**
	 * Returns the serial number of the node.
	 * <p>
	 * See {@link #setSerialNumber(String)} for more details.
	 * 
	 * @return serialNumber The serial number of the node.
	 */
	public final String getSerialNumber() {
		return serialNumber;
	}

	/**
	 * Sets the serial number of the node.
	 * <ul>
	 * <li>If the node is an inner node or an leaf node, use
	 * node.serialNumber(), <br>
	 * see {@link de.uka.ilkd.key.proof.Node#serialNr()}</li>
	 * <li>If the node is a branch node, use
	 * node.getNodeInfo().getBranchLabel().replace(" ","_"), <br>
	 * see {@link de.uka.ilkd.key.proof.NodeInfo#getBranchLabel()}.</li>
	 * </ul>
	 * 
	 * @param serial
	 *            The serial number to set.
	 */
	public final void setSerialNumber(final String serial) {
		this.serialNumber = serial;
	}

	/**
	 * Indicates whether the goal corresponding to the node is open or closed.
	 * <br>
	 * See {@link de.uka.ilkd.key.proof.Node#isClosed()}.
	 * 
	 * @return closed is TRUE when the goal is closed, else FALSE.
	 */
	public final boolean isClosed() {
		return closed;
	}

	/**
	 * Defines whether the goal corresponding to the node is open or closed. See
	 * {@link de.uka.ilkd.key.proof.Node#isClosed()}.
	 * 
	 * @param isClosed
	 *            sets the status of the goal, can be open (T) or closed (F)
	 */
	public final void setClosed(final boolean isClosed) {
		this.closed = isClosed;
	}

	/**
	 * Indicates whether the node is linked. <br>
	 * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
	 * 
	 * @return isLinked is TRUE when the node is a linked node, else FALSE.
	 */
	public final boolean isLinked() {
		return linked;
	}

	/**
	 * Defines if the node is a linked node. <br>
	 * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
	 * 
	 * @param isLinked
	 *            should be TRUE if the node is a linked node, else FALSE.
	 */
	public final void setLinked(final boolean isLinked) {
		this.linked = isLinked;
	}

	/**
	 * Indicates if the node is an interactive node. <br>
	 * See {@link de.uka.ilkd.key.proof.Goal#isAutomatic()}. If the node is not
	 * automatic, it is interactive.
	 * 
	 * @return interactive is TRUE when the node is an interactive node, else
	 *         FALSE.
	 */
	public final boolean isInteractive() {
		return interactive;
	}

	/**
	 * Defines whether the node has an active statement. <br>
	 * See {@link de.uka.ilkd.key.proof.Goal#isAutomatic()}. If the node is not
	 * automatic, it is interactive.
	 * 
	 * @param interactive
	 *            should be set to TRUE if the node has an active statement,
	 *            else to FALSE.
	 */
	public final void setInteractive(final boolean interactive) {
		this.interactive = interactive;
	}

	/**
	 * Indicates if the node has an active statement. <br>
	 * See {@link de.uka.ilkd.key.proof.NodeInfo#getActiveStatement()}.
	 * 
	 * @return active is TRUE when the node has an active statement, else to
	 *         FALSE.
	 */
	public final boolean isActive() {
		return active;
	}

	/**
	 * Sets the active statement status of the node. <br>
	 * See {@link de.uka.ilkd.key.proof.NodeInfo#getActiveStatement()}.
	 * 
	 * @param active
	 *            Should be set on TRUE if the node has an active statement,
	 *            else to FALSE.
	 */
	public final void setActive(final boolean active) {
		this.active = active;
	}

	/**
	 * Indicates whether the node has notes. <br>
	 * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
	 * 
	 * @return hasNotes is TRUE if the node has notes, else FALSE.
	 */
	public final boolean hasNotes() {
		return hasNotes;
	}

	/**
	 * Defines if the node has notes. <br>
	 * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
	 * 
	 * @param hasNotes
	 *            should be set to TRUE if the node has notes, else to FALSE.
	 */
	public final void setHasNotes(final boolean hasNotes) {
		this.hasNotes = hasNotes;
	}

	/**
	 * Retrieves the label (name) of the node. <br>
	 * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
	 * 
	 * @return label The name of the node as String.
	 */
	public final String getLabel() {
		return label;
	}

	/**
	 * Sets the label (name) of the node. <br>
	 * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
	 * 
	 * @param label
	 *            The name as String.
	 */
	public final void setLabel(final String label) {
		this.label = label;
	}

	/**
	 * Returns the parent node of the current node.
	 * 
	 * @return the parent NUINode
	 */
	public final NUINode getParent() {
		return parent;
	}

	/**
	 * Sets the parent node of the current node.
	 * 
	 * @param parent
	 *            the parent NUINode
	 */
	public final void setParent(final NUINode parent) {
		this.parent = parent;
	}

	/**
	 * Sets the highlighted field of the node.
	 * 
	 * @param isHighlighted
	 *            marks if the node should be highlighted
	 */
	public final void setHighlighting(final boolean isHighlighted) {
		this.isHighlighted = isHighlighted;
	}

	/**
	 * Returns information about the node's highlighting property.
	 * 
	 * @return true if the node is highlighted, else false
	 */
	public final boolean isHighlighted() {
		return isHighlighted;
	}

	/**
	 * Sets the visibility of the node.
	 * 
	 * @param isVisible
	 *            the state of visibility
	 */
	public final void setVisibility(final boolean isVisible) {
		this.isVisible = isVisible;
	}

	/**
	 * Indicates if the node is visible.
	 * 
	 * @return true if the node is visible, else false
	 */
	public final boolean isVisible() {
		return isVisible;
	}
}
