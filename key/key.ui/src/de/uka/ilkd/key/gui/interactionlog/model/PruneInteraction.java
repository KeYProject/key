package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

public class PruneInteraction extends NodeInteraction {

    public PruneInteraction(Node node) {
        super(node);
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder("prune");

        sb.append("\n\t");
        sb.append(getSerialNr());

        sb.append(";");
        return sb.toString();
    }

    @Override
    public String toString() {
        return "prune;";
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
            .append("------\n")
            .append("## PruneInteraction ")
            .append(getNodeId())
            .append("\n\n");

        return sb.toString();
    }


}
