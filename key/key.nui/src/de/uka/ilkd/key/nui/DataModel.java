package de.uka.ilkd.key.nui;

import java.util.HashMap;
import java.util.Observable;

import de.uka.ilkd.key.proof.Proof;

/**
 * Class representing the data associated with the GUI.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class DataModel extends Observable {

    /**
     * HashMap storing the pairs of (String, {@link TreeViewState}), where
     * String represents the filename of the proof file.
     */
    private HashMap<String, TreeViewState> treeViewStates = new HashMap<String, TreeViewState>();

    /**
     * Represents the lastly stored TreeViewState, therefore it is displayed
     * currently in the TreeView
     */
    private TreeViewState loadedTreeViewState;

    /**
     * Returns the {@link TreeViewState} associated to the given filename name.
     * 
     * @param name
     *            The key used to search for the TreeViewState.
     * @return TreeViewState The TreeViewState searched for.
     */
    public TreeViewState getTreeViewState(String name) {
        return treeViewStates.get(name);
    }

    /**
     * Stores a <b>new</b> TreeViewState into the list of TreeViewStates.
     * Overwrites the an existing state if the key is already present. Do NOT
     * use this method to save changes of a proof file, use instead
     * {@link #updateProofFile}.
     * 
     * @param treeViewState
     *            The new treeViewState to store.
     * @param name
     *            The name of the key associated with the state (filename of
     *            proof file).
     */
    public void saveTreeViewState(TreeViewState treeViewState, String name) {
        treeViewStates.put(name, treeViewState);
        loadedTreeViewState = treeViewState;
        this.setChanged();
        this.notifyObservers(name);
    }

    /**
     * Updates the proof file of an already existing (loaded) TreeViewState.
     * 
     * @param key
     *            the key (filename) of the {@link Proof} file.
     * @param proof
     *            the proof file to be set to the TreeViewState, identified by
     *            the provided key
     * 
     */
    public void updateProofFile(String key, Proof proof) {
        TreeViewState treeViewState = treeViewStates.get(key);
        if (treeViewState != null) {
            treeViewState.setProof(proof);
            treeViewState.setModified(true);
            this.setChanged();
            this.notifyObservers(key);
        }
    }

    /**
     * @return
     */
    public TreeViewState getLoadedTreeViewState() {
        return loadedTreeViewState;
    }

}
