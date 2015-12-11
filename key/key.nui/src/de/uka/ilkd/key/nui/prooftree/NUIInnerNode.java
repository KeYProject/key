package de.uka.ilkd.key.nui.prooftree;

public class NUIInnerNode extends NUINode {

    private de.uka.ilkd.key.proof.Node proofNode;

    /**
     * @param proofNode
     */
    public NUIInnerNode(de.uka.ilkd.key.proof.Node proofNode) {
        this.proofNode = proofNode;
    }

    /**
     * @return the proofNode
     */
    public de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
