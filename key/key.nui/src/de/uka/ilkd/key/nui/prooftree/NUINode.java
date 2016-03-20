package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.nui.prooftree.ProofTreeStyler.StyleConfiguration;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.value.ChangeListener;

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
public abstract class NUINode implements Cloneable {
    /**
     * Marks if the node has the active property.
     */
    private final SimpleBooleanProperty active = new SimpleBooleanProperty();
    /**
     * Marks if the node has the closed property.
     */
    private final SimpleBooleanProperty closed = new SimpleBooleanProperty();

    /**
     * Marks if the node has the interactive property.
     */
    private final SimpleBooleanProperty interactive = new SimpleBooleanProperty();

    /**
     * The node text label.
     */
    private final SimpleStringProperty label = new SimpleStringProperty();

    /**
     * Marks if the node has the linked property.
     */
    private final SimpleBooleanProperty linked = new SimpleBooleanProperty(false);

    /**
     * Marks if notes for this node exist.
     */
    private final SimpleBooleanProperty notes = new SimpleBooleanProperty(false);

    /**
     * the parent node of this node.
     */
    private final SimpleObjectProperty<NUINode> parent = new SimpleObjectProperty<>();

    /**
     * Marks whether this node is a result of a currently active search.
     */
    private final SimpleBooleanProperty searchResult = new SimpleBooleanProperty(false);

    /**
     * The serial number of the proof node.
     */
    private final SimpleStringProperty serialNumber = new SimpleStringProperty();

    /**
     * The {@link StyleConfiguration} of the NUINode.
     */
    private StyleConfiguration style;

    /**
     * Marks if the node is a symbolic execution.
     */
    private final SimpleBooleanProperty symbolicExecution = new SimpleBooleanProperty(false);

    /**
     * Marks if the node is currently visible in the treeView.
     */
    private final SimpleBooleanProperty visible = new SimpleBooleanProperty(true);

    /**
     * Adds a search result listener that is notified when the node is marked as
     * search result.
     * 
     * @param listener
     *            the changeListener to add.
     */
    public void addSearchResultListener(final ChangeListener<Boolean> listener) {
        searchResult.addListener(listener);
    }

    /**
     * Returns the nodes of the subtree rooted by the this node, including this
     * node itself.
     * 
     * @return a {@link List} of NUINodes.
     */
    public List<NUINode> asList() {
        final List<NUINode> list = new LinkedList<>();
        list.add(this);
        return list;
    }

    /**
     * Clones the NUINode. Attention, normally the parent is not set because the
     * cloned one is not known.
     * 
     * @return the cloned nuiNode
     */
    @Override
    public abstract NUINode clone() throws CloneNotSupportedException;


    /**
     * Retrieves the label (name) of the node. <br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @return label The name of the node as String.
     */
    public final String getLabel() {
        return label.get();
    }

    /**
     * Returns the parent node of the current node.
     * 
     * @return the parent NUINode
     */
    public final NUINode getParent() {
        return parent.get();
    }

    /**
     * Returns the serial number of the node.
     * <p>
     * See {@link #setSerialNumber(String)} for more details.
     * 
     * @return serialNumber The serial number of the node.
     */
    public final String getSerialNumber() {
        return serialNumber.get();
    }

    /**
     * TODO
     * @return
     */
    public StyleConfiguration getStyle() {
        return style;
    }

    /**
     * Returns the assigned {@link StyleConfiguration} of this node.
     * 
     * @return StyleConfiguration assigned to this node.
     */
    public StyleConfiguration getStyleConfiguration() {
        return this.style;
    }

    /**
     * Indicates whether the node has notes. <br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @return hasNotes is TRUE if the node has notes, else FALSE.
     */
    public final boolean hasNotes() {
        return notes.get();
    }

    /**
     * Indicates if the node has an active statement. <br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getActiveStatement()}.
     * 
     * @return active is TRUE when the node has an active statement, else to
     *         FALSE.
     */
    public final boolean isActive() {
        return active.get();
    }

    /**
     * Indicates whether the goal corresponding to the node is open or closed.
     * <br>
     * See {@link de.uka.ilkd.key.proof.Node#isClosed()}.
     * 
     * @return closed is TRUE when the goal is closed, else FALSE.
     */
    public final boolean isClosed() {
        return closed.getValue();
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
        return interactive.get();
    }

    /**
     * Indicates whether the node is linked. <br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @return isLinked is TRUE when the node is a linked node, else FALSE.
     */
    public final boolean isLinked() {
        return linked.get();
    }

    /**
     * @return Whether there are any notes for this node.
     */
    public boolean isNotes() {
        return notes.get();
    }

    /**
     * Returns the value of the property isSearchResult.
     * 
     * @return true if this is a search Result, otherwise false
     */
    public boolean isSearchResult() {
        return searchResult.get();
    }

    /**
     * Indicates if the node has is an symbolic execution.
     * 
     * @return true iff the node is an symbolic execution.
     */
    public final boolean isSymbolicExecution() {
        return symbolicExecution.get();
    }

    /**
     * Indicates if the node is visible.
     * 
     * @return true if the node is visible, otherwise false
     */
    public final boolean isVisible() {
        return visible.get();
    }

    /**
     * Removes a search result listener.
     * 
     * @param listener
     *            the changeListener to remove
     */
    public void removeSearchResultListener(final ChangeListener<Boolean> listener) {
        searchResult.removeListener(listener);
    }

    /**
     * Marks all nodes in the subtree beneath this node as non-search-Results.
     */
    public void resetSearch() {
        setSearchResult(false);
    }

    /**
     * Searches the subtree beneath this NUINode for all occurrences of the term
     * and marks each of them as SearchResults.
     * 
     * @param term
     *            the term to search for
     * @return true iff there are any search results
     */
    public int search(final String term) {
        if (term.isEmpty()) {
            return 0;
        }

        final boolean match = getLabel().toLowerCase().contains(term.toLowerCase());
        setSearchResult(match);
        return match ? 1 : 0;
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
        this.active.set(active);
    }

    /**
     * Defines whether the goal corresponding to the node is open or closed. See
     * {@link de.uka.ilkd.key.proof.Node#isClosed()}.
     * 
     * @param isClosed
     *            sets the status of the goal, can be open (T) or closed (F)
     */
    public final void setClosed(final boolean isClosed) {
        this.closed.set(isClosed);
    }

    /**
     * Defines if the node has notes. <br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @param hasNotes
     *            should be set to TRUE if the node has notes, else to FALSE.
     */
    public final void setHasNotes(final boolean hasNotes) {
        this.notes.set(hasNotes);
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
        this.interactive.set(interactive);
    }

    /**
     * Sets the label (name) of the node. <br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @param label
     *            The name as String.
     */
    public final void setLabel(final String label) {
        this.label.set(label);
    }

    /**
     * Defines if the node is a linked node. <br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @param isLinked
     *            should be TRUE if the node is a linked node, otherwise FALSE.
     */
    public final void setLinked(final boolean isLinked) {
        this.linked.set(isLinked);
    }

    /* ********** SEARCH METHODS ********** */

    /**
     * Sets the parent node of the current node.
     * 
     * @param parent
     *            the parent NUINode
     */
    public final void setParent(final NUINode parent) {
        this.parent.set(parent);
    }

    /**
     * Defines if the node is marked as a search result.
     * 
     * @param isSearchResult
     *            true iff the NUINode is part of a searchResult
     */
    public void setSearchResult(final boolean isSearchResult) {
        this.searchResult.set(isSearchResult);
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
        this.serialNumber.set(serial);
    }

    /**
     * TODO
     * @param style
     */
    public void setStyle(final StyleConfiguration style) {
        this.style = style;
    }

    /**
     * Defines whether the node is a symbolic execution.
     * 
     * @param state
     *            has to be TRUE iff the node is a symbolic execution.
     */
    public final void setSymbolicExcecution(final boolean state) {
        this.symbolicExecution.set(state);
    }

    /**
     * Sets the visibility of the node.
     * 
     * @param isVisible
     *            the state of visibility
     */
    public final void setVisibility(final boolean isVisible) {
        this.visible.set(isVisible);
    }

    /**
     * Converts a NUINode to String.
     */
    @Override
    public String toString() {
        return getLabel();
    }

    /**
     * Copies the fields of a NUINode to another.
     * 
     * @param source
     *            the source of the field values
     * @param target
     *            the target where the fields have to be set.
     */
    protected void copyFields(final NUINode source, final NUINode target) {
        source.setActive(target.isActive());
        source.setClosed(target.isClosed());
        source.setHasNotes(target.hasNotes());
        source.setInteractive(target.isInteractive());
        source.setLabel(target.getLabel());
        source.setLinked(target.isLinked());
        source.setSerialNumber(target.getSerialNumber());
    }

    /**
     * Determines and sets the {@link StyleConfiguration} of this node. This
     * configuration is later applied to the rendered {@link ProofTreeCell}.
     * <p>
     * 
     * This 'caching' of the style configuration is required for testing
     * purposes.
     */
    protected void setStyleConfiguration() {

        this.style = new ProofTreeStyler().getStyleConfiguration(this);

    }

}
