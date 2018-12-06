package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

public class PruneInteraction extends NodeInteraction {

    protected PruneInteraction(Node node) {
        super(node);
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder("prune");

        sb.append("\n\t");
        sb.append(getNode().serialNr());

        sb.append(";");
        return sb.toString();
    }

}
