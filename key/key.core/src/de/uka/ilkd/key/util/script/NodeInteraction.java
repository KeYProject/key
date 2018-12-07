package de.uka.ilkd.key.util.script;

import java.beans.Transient;
import java.util.Date;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public abstract class NodeInteraction implements Interaction {
    private transient int serialNr;

    private Date created = new Date();

    private NodeIdentifier nodeId;

    public NodeInteraction() { }

    protected NodeInteraction(Node node) {
        this.serialNr = node.serialNr();
        this.nodeId = NodeIdentifier.get(node);
    }

    @Override
    public Date created() { return created; }

    @Transient(true)
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

    public Date getCreated() {
        return created;
    }

    public void setCreated(Date created) {
        this.created = created;
    }
}
