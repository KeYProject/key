package org.key_project.ui.interactionlog.model;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.Optional;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class PruneInteraction extends NodeInteraction {
    private static final long serialVersionUID = -8499747129362589793L;

    public PruneInteraction() {
    }

    public PruneInteraction(Node node) {
        super(node);
    }

    @Override
    public String toString() {
        return "prune";
    }

    @Override
    public String getMarkdown() {
        return String.format("## Prune%n%n"
                + "**Date**: %s%n"
                + "prune to node %s%n", getCreated(), getNodeId());
    }

    @Override
    public String getProofScriptRepresentation() {
        return String.format("prune %s%n", getNodeId());
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        Optional<Node> node = getNodeId().findNode(goal.proof());
        node.ifPresent(node1 -> goal.proof().pruneProof(node1));
    }
}
