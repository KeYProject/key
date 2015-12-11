package de.uka.ilkd.key.prooftree;

public abstract class Node {
    private int id;
    private String label;
    private boolean closed;
    private boolean linked;
    private boolean interactive;
    private boolean active;
    private boolean hasNotes;
    
    /**
     * @return the closed
     */
    public boolean isClosed() {
        return closed;
    }
    /**
     * @param closed the closed to set
     */
    public void setClosed(boolean closed) {
        this.closed = closed;
    }
    /**
     * @return the linked
     */
    public boolean isLinked() {
        return linked;
    }
    /**
     * @param linked the linked to set
     */
    public void setLinked(boolean linked) {
        this.linked = linked;
    }
    /**
     * @return the interactive
     */
    public boolean isInteractive() {
        return interactive;
    }
    /**
     * @param interactive the interactive to set
     */
    public void setInteractive(boolean interactive) {
        this.interactive = interactive;
    }
    /**
     * @return the active
     */
    public boolean isActive() {
        return active;
    }
    /**
     * @param active the active to set
     */
    public void setActive(boolean active) {
        this.active = active;
    }
    /**
     * @return true if there are notes
     */
    public boolean hasNotes() {
        return hasNotes;
    }
    /**
     * @param hasNotes the hasNotes to set
     */
    public void setHasNotes(boolean hasNotes) {
        this.hasNotes = hasNotes;
    }
    /**
     * @return the id
     */
    public int getId() {
        return id;
    }
    /**
     * @param id the id to set
     */
    public void setId(int id) {
        this.id = id;
    }
    /**
     * @return the label
     */
    public String getLabel() {
        return label;
    }
    /**
     * @param label the label to set
     */
    public void setLabel(String label) {
        this.label = label;
    }
}
