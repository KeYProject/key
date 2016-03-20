package de.uka.ilkd.key.nui;

import de.uka.ilkd.key.nui.prooftree.ProofTreeItem;
import de.uka.ilkd.key.proof.Proof;

/**
 * Class representing a state of the TreeView.
 * 
 * @author Florian Breitfelder
 * @author Patrick Jattke
 *
 */
public class TreeViewState {

    /**
     * The proof file of the state.
     */
    private Proof proof;

    /**
     * The generated tree, associated with the proof.
     */
    private final ProofTreeItem treeItem;

    /**
     * Indicates whether the proof was modified after loading it into the
     * treeView.
     */
    private boolean isModified;

    /**
     * Creates a new TreeViewState.
     * 
     * @param proof
     *            The proof file of the state.
     * 
     * @param treeItem
     *            The tree associated with the proof.
     */
    public TreeViewState(final Proof proof, final ProofTreeItem treeItem) {
        this.proof = proof;
        this.treeItem = treeItem;
    }

    /**
     * Returns the {@link Proof} file of the TreeViewState.
     * 
     * @return Proof The proof file of the TreeViewState.
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the {@link ProofTreeItem} of the TreeViewState.
     * 
     * @return TreeItem&lt;NUINode&gt; the root node of the tree.
     */
    public ProofTreeItem getTreeItem() {
        return treeItem;
    }

    /**
     * Indicates whether the proof of the TreeViewState was changed after
     * loading it initially. This information is used to show the confirmation
     * dialog before closing KeY, if the loaded proof was modified during the
     * session.
     * 
     * @param bool
     *            Sets the status of the proof file to bool, where TRUE marks
     *            the file as changed and FALSE as unchanged.
     */
    protected void setModified(final boolean bool) {
        this.isModified = bool;
    }

    /**
     * Returns TRUE if the proof of the TreeViewState was modified after loading
     * or after last saving it, else returns FALSE.
     * 
     * @return the status of the changes at the proof file.
     */
    public boolean isModified() {
        return this.isModified;
    }

    /**
     * Sets a new proof file to the TreeViewState. Overwrites the existing proof
     * file.
     * 
     * @param proof
     *            the proof to be added to the TreeViewState.
     */
    protected void setProof(final Proof proof) {
        this.proof = proof;
    }

}
