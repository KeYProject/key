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
    private Proof proof = null;

    /**
     * The generated tree, associated with the proof.
     */
    private ProofTreeItem treeItem = null;

    /**
     * Creates a new TreeViewState.
     * 
     * @param proof
     *            The proof file of the state.
     * 
     * @param treeItem
     *            The tree associated with the proof.
     */
    public TreeViewState(Proof proof, ProofTreeItem treeItem) {
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

}
