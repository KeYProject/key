package de.uka.ilkd.key.core;


/**
 * The KeYSelectionListener is notified if the proof or the node the user works with has changed.
 */
public interface KeYSelectionListener {

    /** focused node has changed */
    void selectedNodeChanged(KeYSelectionEvent e);

    /**
     * the selected proof has changed (e.g. a new proof has been loaded)
     */
    void selectedProofChanged(KeYSelectionEvent e);

}
