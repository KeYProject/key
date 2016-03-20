package de.uka.ilkd.key.nui.prooftree;

/**
 * Represents an inner node. Is used to create a graphical representation of a
 * proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUIInnerNode extends NUINode {

    /**
     * The related proof node of the inner node.
     */
    private final de.uka.ilkd.key.proof.Node proofNode;

    /**
     * Creates a new inner node.
     * 
     * @param pNode
     *            The related proof node of the inner node.
     */
    public NUIInnerNode(final de.uka.ilkd.key.proof.Node pNode) {
        super();
        this.proofNode = pNode;
    }

    /**
     * Returns the proof node of the inner node.
     * 
     * @return proofNode The proof node of the inner node.
     */
    public final de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }

    @Override
    public NUIInnerNode clone() {
        // create clone
        final NUIInnerNode cloned = new NUIInnerNode(proofNode);
        this.copyFields(this, cloned);

        return cloned;
    }
}
