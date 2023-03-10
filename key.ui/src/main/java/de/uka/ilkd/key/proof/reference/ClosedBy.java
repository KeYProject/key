package de.uka.ilkd.key.proof.reference;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Indicates that a branch has been closed by "reference" to another closed proof.
 *
 * @author Arne Keller
 */
public class ClosedBy {
    /**
     * The proof referenced.
     */
    private Proof proof;
    /**
     * The node referenced.
     */
    private Node node;

    public ClosedBy(Proof proof, Node node) {
        this.proof = proof;
        this.node = node;
    }
}
