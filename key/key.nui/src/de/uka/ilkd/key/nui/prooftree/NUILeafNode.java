package de.uka.ilkd.key.nui.prooftree;

/**
 * Represents a leaf node. Is used to create a graphical representation of
 * a proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUILeafNode extends NUINode {

    /**
     * The related proof node of the leaf node.
     */
    private de.uka.ilkd.key.proof.Node proofNode;

    /**
     * Creates a new leaf node.
     * 
     * @param proofNode
     * 		   The related proof node of the leaf node.
     */
    public NUILeafNode(de.uka.ilkd.key.proof.Node proofNode) {
        this.proofNode = proofNode;
    }

    /**
     * Returns the proof node of the leaf node.
     * 
     * @return proofNode
     * 			The proof node of the leaf node.
     */
    public de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
