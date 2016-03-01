package de.uka.ilkd.key.nui;

import java.util.HashMap;
import java.util.Observable;

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
     * Stores a new TreeViewState into the list of TreeViewStates. Overwrites
     * the last state if the key is already present.
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

    public TreeViewState getLoadedTreeViewState() {
        return loadedTreeViewState;
    }

}
