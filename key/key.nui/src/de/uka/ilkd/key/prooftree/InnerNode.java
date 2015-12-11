package de.uka.ilkd.key.prooftree;

public class InnerNode extends Node {

    private de.uka.ilkd.key.proof.Node proofNode;

    /**
     * @param proofNode
     */
    public InnerNode(de.uka.ilkd.key.proof.Node proofNode) {
        this.proofNode = proofNode;
    }

    /**
     * @return the proofNode
     */
    public de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
