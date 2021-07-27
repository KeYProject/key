package org.key_project.ui.interactionlog.model;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.ui.interactionlog.api.Interaction;

import javax.xml.bind.annotation.XmlTransient;
import java.beans.Transient;

@XmlTransient
public abstract class NodeInteraction extends Interaction {
    private static final long serialVersionUID = 1L;

    private transient int serialNr;

    private NodeIdentifier nodeId;

    public NodeInteraction() { }

    protected NodeInteraction(Node node) {
        this.serialNr = node.serialNr();
        this.nodeId = NodeIdentifier.get(node);
    }

    @Transient()
    public int getSerialNr() {
        return serialNr;
    }

    public NodeIdentifier getNodeId() {
        return nodeId;
    }

    public void setNodeId(NodeIdentifier nodeId) {
        this.nodeId = nodeId;
    }

    public Node getNode(Proof proof) {
        return nodeId.findNode(proof).orElse(null);
    }
}
