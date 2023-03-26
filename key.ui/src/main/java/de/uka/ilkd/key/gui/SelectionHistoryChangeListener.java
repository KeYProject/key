package de.uka.ilkd.key.gui;

/**
 * Simple interface to be notified about all changes to the selection history.
 *
 * @author Arne Keller
 */
public interface SelectionHistoryChangeListener {
    /**
     * Update state. Called whenever the history is modified.
     */
    void update();
}
