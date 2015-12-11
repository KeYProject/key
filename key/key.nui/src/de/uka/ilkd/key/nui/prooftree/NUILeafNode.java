package de.uka.ilkd.key.nui.prooftree;

public class NUILeafNode extends NUINode {

    private de.uka.ilkd.key.proof.Node proofNode;

    /**
     * @param proofNode
     */
    public NUILeafNode(de.uka.ilkd.key.proof.Node proofNode) {
        this.proofNode = proofNode;
    }

    /**
     * @return the proofNode
     */
    public de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
