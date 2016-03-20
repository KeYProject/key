package de.uka.ilkd.key.nui.prooftree;

/**
 * Represents a leaf node. Is used to create a graphical representation of a
 * proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUILeafNode extends NUINode {

    /**
     * The related proof node of the leaf node.
     */
    private final de.uka.ilkd.key.proof.Node proofNode;

    /**
     * Creates a new leaf node.
     * 
     * @param proofNode
     *            The related proof node of the leaf node.
     */
    public NUILeafNode(final de.uka.ilkd.key.proof.Node proofNode) {
        super();
        this.proofNode = proofNode;
    }

    /**
     * Returns the corresponding proof node of the leaf node.
     * 
     * @return proofNode The proof node of the leaf node.
     */
    public final de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }

    @Override
    public NUILeafNode clone(){
        // create clone
        final NUILeafNode cloned = new NUILeafNode(proofNode);
        this.copyFields(this, cloned);

        return cloned;
    }
}
