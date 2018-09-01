package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

/**
 * @author weigl
 */
public abstract class Interaction {
    private final Node node;

    protected Interaction(Node node) {
        this.node = node;
    }

    public abstract String getProofScriptRepresentation(Services services);

    public Node getNode() {
        return node;
    }
}