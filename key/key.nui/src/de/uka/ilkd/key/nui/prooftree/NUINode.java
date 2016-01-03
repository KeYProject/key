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

    private String label;
    private boolean closed = false;
    private boolean linked = false;
    private boolean interactive = false;
    private boolean active = false;
    private boolean hasNotes = false;
    private String serialNumber;

    /**
     * Returns the serial number of the node. </br>
     * See {@link #setSerialNumber(String)} for more details.
     * 
     * @return serialNumber The serial number of the node.
     */
    public String getSerialNumber() {
        return serialNumber;
    }

    /**
     * Sets the serial number of the node.
     * <ul>
     * <li>If the node is an inner node or an leaf node, use
     * node.serialNumber(), </br> see {@link de.uka.ilkd.key.proof.Node#serialNr()}</li>
     * <li>If the node is a branch node, use node.getNodeInfo().getBranchLabel().replace(" ","_"), </br> see
     * {@link de.uka.ilkd.key.proof.NodeInfo#getBranchLabel()}.
     * </li>
     * </ul>
     * 
     * @param serial
     *            The serial number to set.
     */
    public void setSerialNumber(String serial) {
        this.serialNumber = serial;
    }

    /**
     * Indicates whether the goal corresponding to the node is open or
     * closed. </br>
     * See {@link de.uka.ilkd.key.proof.Node#isClosed()}.
     * 
     * @return closed is TRUE when the goal is closed, else FALSE.
     */
    public boolean isClosed() {
        return closed;
    }

    /**
     * Defines whether the goal corresponding to the node is open or
     * closed. </br>
     * See {@link de.uka.ilkd.key.proof.Node#isClosed()}.
     * 
     * @param isClosed
     *            sets the status of the goal, can be open (TRUE) or closed
     *            (FALSE).
     */
    public void setClosed(boolean isClosed) {
        this.closed = isClosed;
    }

    /**
     * Indicates whether the node is linked. </br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @return isLinked is TRUE when the node is a linked node, else FALSE.
     */
    public boolean isLinked() {
        return linked;
    }

    /**
     * Defines if the node is a linked node. </br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @param isLinked
     *            should be TRUE if the node is a linked node, else FALSE.
     */
    public void setLinked(boolean isLinked) {
        this.linked = isLinked;
    }

    /**
     * Indicates if the node is an interactive node. </br>
     * See {@link de.uka.ilkd.key.proof.Goal#isAutomatic()}. If the node is not
     * automatic, it is interactive.
     * 
     * @return interactive is TRUE when the node is an interactive node, else
     *         FALSE.
     */
    public boolean isInteractive() {
        return interactive;
    }

    /**
     * Defines whether the node has an active statement. </br>
     * See {@link de.uka.ilkd.key.proof.Goal#isAutomatic()}. If the node is not
     * automatic, it is interactive.
     * 
     * @param interactive
     *            should be set to TRUE if the node has an active statement,
     *            else to FALSE.
     */
    public void setInteractive(boolean interactive) {
        this.interactive = interactive;
    }

    /**
     * Indicates if the node has an active statement. </br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getActiveStatement()}.
     * 
     * @return active is TRUE when the node has an active statement, else to
     *         FALSE.
     */
    public boolean isActive() {
        return active;
    }

    /**
     * Sets the active statement status of the node. </br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getActiveStatement()}.
     * 
     * @param active
     *            Should be set on TRUE if the node has an active statement,
     *            else to FALSE.
     */
    public void setActive(boolean active) {
        this.active = active;
    }

    /**
     * Indicates whether the node has notes. </br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @return hasNotes is TRUE if the node has notes, else FALSE.
     */
    public boolean hasNotes() {
        return hasNotes;
    }

    /**
     * Defines if the node has notes. </br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @param hasNotes
     *            should be set to TRUE if the node has notes, else to FALSE.
     */
    public void setHasNotes(boolean hasNotes) {
        this.hasNotes = hasNotes;
    }

    /**
     * Retrieves the label (name) of the node. </br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @return label The name of the node as String.
     */
    public String getLabel() {
        return label;
    }

    /**
     * Sets the label (name) of the node. </br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @param label
     *            The name as String.
     */
    public void setLabel(String label) {
        this.label = label;
    }
}
