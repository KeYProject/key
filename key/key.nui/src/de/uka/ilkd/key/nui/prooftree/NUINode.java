package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.List;
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
    private SimpleBooleanProperty active;
    /**
     * Marks if the node has the closed property.
     */
    private SimpleBooleanProperty closed;

    /**
     * Marks if the node has the interactive property.
     */
    private SimpleBooleanProperty interactive;

    /**
     * Marks if the node is currently visible in the treeView.
     */
    private SimpleBooleanProperty isVisible = new SimpleBooleanProperty(true);

    /**
     * The node text label.
     */
    private SimpleStringProperty label;

    /**
     * Marks if the node has the linked property.
     */
    private SimpleBooleanProperty linked;

    /**
     * Marks if notes for this node exist.
     */
    private SimpleBooleanProperty notes;

    /**
     * the parent node of this node.
     */
    private SimpleObjectProperty<NUINode> parent;

    /**
     * The serial number of the proof node.
     */
    private SimpleStringProperty serialNumber;
    
    /**
     * Marks whether this node is a result of a currently active search.
     */
    private SimpleBooleanProperty isSearchResult = new SimpleBooleanProperty(false);

    /**
     * Retrieves the label (name) of the node. <br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @return label The name of the node as String.
     */
    public final String getLabel() {
        if (label == null) {
            label = new SimpleStringProperty();
        }
        return label.get();
    }

    /**
     * Returns the parent node of the current node.
     * 
     * @return the parent NUINode
     */
    public final NUINode getParent() {
        if (parent == null) {
            parent = new SimpleObjectProperty<NUINode>();
        }
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
        if (serialNumber == null) {
            serialNumber = new SimpleStringProperty();
        }
        return serialNumber.get();
    }

    /**
     * Indicates whether the node has notes. <br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @return hasNotes is TRUE if the node has notes, else FALSE.
     */
    public final boolean hasNotes() {
        if (notes == null) {
            notes = new SimpleBooleanProperty();
        }
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
        if (active == null) {
            active = new SimpleBooleanProperty();
        }
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
        if (closed == null) {
            closed = new SimpleBooleanProperty();
        }
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
        if (interactive == null) {
            interactive = new SimpleBooleanProperty();
        }
        return interactive.get();
    }

    /**
     * Indicates whether the node is linked. <br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @return isLinked is TRUE when the node is a linked node, else FALSE.
     */
    public final boolean isLinked() {
        if (linked == null) {
            linked = new SimpleBooleanProperty();
        }
        return linked.get();
    }

    /**
     * Indicates if the node is visible.
     * 
     * @return true if the node is visible, otherwise false
     */
    public final boolean isVisible() {
        if (isVisible == null) {
            isVisible = new SimpleBooleanProperty();
        }
        return isVisible.get();
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
        if (this.active == null) {
            this.active = new SimpleBooleanProperty(active);
        }
        else {
            this.active.set(active);
        }
    }

    /**
     * Defines whether the goal corresponding to the node is open or closed. See
     * {@link de.uka.ilkd.key.proof.Node#isClosed()}.
     * 
     * @param isClosed
     *            sets the status of the goal, can be open (T) or closed (F)
     */
    public final void setClosed(final boolean isClosed) {
        if (this.closed == null) {
            this.closed = new SimpleBooleanProperty(isClosed);
        }
        else {
            this.closed.set(isClosed);
        }
    }

    /**
     * Defines if the node has notes. <br>
     * See {@link de.uka.ilkd.key.proof.NodeInfo#getNotes()}.
     * 
     * @param hasNotes
     *            should be set to TRUE if the node has notes, else to FALSE.
     */
    public final void setHasNotes(final boolean hasNotes) {
        if (this.notes == null) {
            this.notes = new SimpleBooleanProperty(hasNotes);
        }
        else {
            this.notes.set(hasNotes);
        }
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
        if (this.interactive == null) {
            this.interactive = new SimpleBooleanProperty(interactive);
        }
        else {
            this.interactive.set(interactive);
        }
    }

    /**
     * Sets the label (name) of the node. <br>
     * See {@link de.uka.ilkd.key.proof.Node#serialNr()}.
     * 
     * @param label
     *            The name as String.
     */
    public final void setLabel(final String label) {
        if (this.label == null) {
            this.label = new SimpleStringProperty(label);
        }
        else {
            this.label.set(label);
        }
    }

    /**
     * Defines if the node is a linked node. <br>
     * See {@link de.uka.ilkd.key.proof.Goal#isLinked()}.
     * 
     * @param isLinked
     *            should be TRUE if the node is a linked node, otherwise FALSE.
     */
    public final void setLinked(final boolean isLinked) {
        if (this.linked == null) {
            this.linked = new SimpleBooleanProperty(isLinked);
        }
        else {
            this.linked.set(isLinked);
        }
    }

    /**
     * Sets the parent node of the current node.
     * 
     * @param parent
     *            the parent NUINode
     */
    public final void setParent(final NUINode parent) {
        if (this.parent == null) {
            this.parent = new SimpleObjectProperty<NUINode>(parent);
        }
        else {
            this.parent.set(parent);
        }
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
        if (this.serialNumber == null) {
            this.serialNumber = new SimpleStringProperty(serial);
        }
        else {
            this.serialNumber.set(serial);
        }
    }

    /**
     * Sets the visibility of the node.
     * 
     * @param isVisible
     *            the state of visibility
     */
    public final void setVisibility(final boolean isVisible) {
        if (this.isVisible == null) {
            this.isVisible = new SimpleBooleanProperty(isVisible);
        }
        else {
            this.isVisible.set(isVisible);
        }
    }
    
    /**
     * Clones the NUINode.
     * Attention, normally the parent is not set because the
     * cloned one is not known.
     * @return the cloned nuiNode
     */
    @Override
    public abstract NUINode clone();
    
    /**
     * Copies the fields of a NUINode to another.
     * @param source  the source of the field values
     * @param target  the target where the fields have to be set.
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
     * Converts a NUINode to String.
     */
    @Override
    public String toString() {
        return getLabel();
    }
    
    
    /* ********** SEARCH METHODS ********** */
    
    /**
     * Returns the value of the property isSearchResult.
     * 
     * @return true if this is a search Result, otherwise false
     */
    public boolean isSearchResult() {
        if (isSearchResult == null) {
            isSearchResult = new SimpleBooleanProperty();
        }
        return isSearchResult.get();
    }
    
    /**
     * Defines if the node is marked as a search result.
     * 
     * @param isSearchResult true iff the NUINode is part of a searchResult
     */
    public void setSearchResult(final boolean isSearchResult) {
        if (this.isSearchResult == null) {
            this.isSearchResult = new SimpleBooleanProperty(isSearchResult);
        }
        else {
            this.isSearchResult.set(isSearchResult);
        }
    }
    
    /**
     * Adds a search result listener that is notified when the node is marked as
     * search result.
     * 
     * @param listener
     *            the changeListener to add.
     */
    public void addSearchResultListener(final ChangeListener<Boolean> listener) {
       if (isSearchResult == null) {
           isSearchResult = new SimpleBooleanProperty();
       }
        isSearchResult.addListener(listener);
    }

    /**
     * Removes a search result listener.
     * @param listener the changeListener to remove
     */
    public void removeSearchResultListener(final ChangeListener<Boolean> listener) {
       if (isSearchResult != null) {
            isSearchResult.removeListener(listener);
        }
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
     * @param term  the term to search for
     * @return      true iff there are any search results
     */
    public boolean search(final String term) {
        if (term.isEmpty()) {
            return false;
        }
        
        boolean match = getLabel().toLowerCase().contains(term.toLowerCase());
        setSearchResult(match);
        return match;
    }
    
    //TODO really necessary???
    public List<NUINode> asList() {
        List<NUINode> l = new LinkedList<>();
        l.add(this);
        return l;
    }
}
