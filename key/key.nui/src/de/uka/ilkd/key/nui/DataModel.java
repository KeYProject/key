package de.uka.ilkd.key.nui;

import java.io.File;
import java.io.IOException;
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
     * An instance representing the associated NUI.
     */
    private NUI nui;

    /**
     * Creates a new data model for the GUI instance.
     * 
     * @param nui
     *            The {@link NUI} instance associated to the data model.
     */
    public DataModel(NUI nui) {
        this.nui = nui;
    }

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
     * {@link #updateTreeViewState}.
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
     * Updates the already existing (loaded) TreeViewState.
     * 
     * @param key
     *            the key (filename) of the {@link Proof} file.
     * @param updatedTreeViewState
     *            updatedTreeViewState e. g. running strategy
     * 
     */
    public void updateTreeViewState(String key,
            TreeViewState updatedTreeViewState) {

        updatedTreeViewState.setModified(true);
        treeViewStates.put(key, updatedTreeViewState);
        this.setChanged();
        this.notifyObservers(key);
    }

    /**
     * @return
     */
    public TreeViewState getLoadedTreeViewState() {
        return loadedTreeViewState;
    }

    /**
     * Saves the proof file proof to the given File destinationFile.
     * 
     * @param proof
     *            the {@link Proof} file to be saved.
     * @param destinationFile
     *            the destination {@link File} where the proof is saved to.
     */
    public final void saveProof(Proof proof, File destinationFile) {
        try {
            proof.saveToFile(destinationFile);
            proof.setProofFile(destinationFile);
            nui.updateStatusbar(nui.getStringFromBundle("savedSuccessfully")
                    + " " + destinationFile.getAbsolutePath());
            // If proof is successfully saved, unset isModified flag
            getLoadedTreeViewState().setModified(false);
        }
        catch (IOException e) {
            nui.updateStatusbar(e.getMessage());
        }
    }

}
