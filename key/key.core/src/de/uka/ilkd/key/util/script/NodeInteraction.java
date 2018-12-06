package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

public abstract class NodeInteraction implements Interaction {
    private final Node node;

    protected NodeInteraction(Node node) {
        this.node = node;
    }

    public abstract String getProofScriptRepresentation(Services services);

    public Node getNode() {
        return node;
    }
}