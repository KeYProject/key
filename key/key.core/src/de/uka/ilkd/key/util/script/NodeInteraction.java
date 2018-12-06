package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

public abstract class NodeInteraction implements Interaction {
    private NodeIdentifier node;

    public NodeInteraction() { }

    protected NodeInteraction(NodeIdentifier node) {
        this.node = node;
    }

    public NodeInteraction(Node node) {
        this(NodeIdentifier.get(node));
    }

    public abstract String getProofScriptRepresentation(Services services);

    public NodeIdentifier getNode() {
        return node;
    }
}