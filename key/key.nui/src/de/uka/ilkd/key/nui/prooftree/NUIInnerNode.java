package de.uka.ilkd.key.nui.prooftree;

/**
 * Represents an inner node. Is used to create a graphical representation of
 * a proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUIInnerNode extends NUINode {

    /**
     * The related proof node of the inner node.
     */
    private de.uka.ilkd.key.proof.Node proofNode;

    /**
     * Creates a new inner node. 
     * 
     * @param proofNode
     * 			The related proof node of the inner node.
     */
    public NUIInnerNode(de.uka.ilkd.key.proof.Node proofNode) {
        this.proofNode = proofNode;
    }

    /**
     * Returns the proof node of the inner node.
     * 
     * @return proofNode
     * 			The proof node of the inner node.
     */
    public de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
