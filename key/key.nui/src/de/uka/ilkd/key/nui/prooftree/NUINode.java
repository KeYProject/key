package de.uka.ilkd.key.nui.prooftree;

/**
 * Abstract class for representing a NUINode, which can be:
 * <ul>
 * <li>a NUIBranchNode {@link de.uka.ilkd.key.nui.prooftree.NUIBranchNode}</li>
 * <li>a NUILeafNode {@link de.uka.ilkd.key.nui.prooftree.NUILeafNode}</li>
 * <li>a NUIInnerNode {@link de.uka.ilkd.key.nui.prooftree.NUIInnerNode}</li>
 * </ul>
 * 
 * @author Matthias Schultheis, Patrick Jattke
 *
 */
public abstract class NUINode {
    private String label;
    private boolean closed = false;
    private boolean linked = false;
    private boolean interactive = false;
    private boolean active = false;
    private boolean hasNotes = false;

    /**
     * Indicates whether the goal corresponding to the node is open or closed
     * 
     * @return closed is TRUE when the goal is closed, else FALSE
     */
    public boolean isClosed() {
        return closed;
    }

    /**
     * Defines whether the goal corresponding to the node is open or closed
     * 
     * @param isClosed
     *            sets the status of the goal, can be open (TRUE) or closed
     *            (FALSE)
     */
    public void setClosed(boolean isClosed) {
        this.closed = isClosed;
    }

    /**
     * Indicates whether the node is linked
     * 
     * @return isLinked is TRUE when the node is a linked node, else FALSE
     */
    public boolean isLinked() {
        return linked;
    }

    /**
     * Defines if the node is a linked node
     * 
     * @param isLinked
     *            should be TRUE if the node is a linked node, else FALSE
     */
    public void setLinked(boolean isLinked) {
        this.linked = isLinked;
    }

    /**
     * Indicates if the node is an interactive node
     * 
     * @return interactive is TRUE when the node is an interactive node, else
     *         FALSE
     */
    public boolean isInteractive() {
        return interactive;
    }

    /**
     * Defines whether the node has an active statement
     * 
     * @param interactive
     *            should be set to TRUE if the node has an active statement,
     *            else to FALSE
     */
    public void setInteractive(boolean interactive) {
        this.interactive = interactive;
    }

    /**
     * Indicates if the node has an active statement
     * 
     * @return active is TRUE when the node has an active statement, else to
     *         FALSE
     */
    public boolean isActive() {
        return active;
    }

    /**
     * Sets
     * 
     * @param active
     *            the active to set
     */
    public void setActive(boolean active) {
        this.active = active;
    }

    /**
     * Indicates whether the node has notes
     * 
     * @return hasNotes is TRUE if the node has notes, else FALSE
     */
    public boolean hasNotes() {
        return hasNotes;
    }

    /**
     * Defines if the node has notes
     * 
     * @param hasNotes
     *            should be set to TRUE if the node has notes, else to FALSE
     */
    public void setHasNotes(boolean hasNotes) {
        this.hasNotes = hasNotes;
    }

    /**
     * Retrieves the label (name) of the node
     * 
     * @return label The name of the node as String
     */
    public String getLabel() {
        return label;
    }

    /**
     * Sets the label (name) of the node
     * 
     * @param label
     *            The name as String
     */
    public void setLabel(String label) {
        this.label = label;
    }
}
