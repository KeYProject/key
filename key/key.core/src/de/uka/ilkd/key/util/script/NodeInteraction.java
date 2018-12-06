package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.proof.Node;

public abstract class NodeInteraction implements Interaction {
    private Node node;

    private NodeIdentifier nodeId;

    public NodeInteraction() { }

    protected NodeInteraction(Node node) {
        this.node = node;
        this.nodeId = NodeIdentifier.get(node);
    }

    public Node getNode() {
        return node;
    }

    public NodeIdentifier getNodeId() {
        return nodeId;
    }
}
