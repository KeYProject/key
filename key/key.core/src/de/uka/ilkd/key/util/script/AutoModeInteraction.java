package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

public class AutoModeInteraction extends Interaction {
    public AutoModeInteraction(Node node) {
        super(node);
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        return "auto;";
    }
}
