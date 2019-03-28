package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class PruneInteraction extends NodeInteraction {
    public PruneInteraction() {
    }

    public PruneInteraction(Node node) {
        super(node);
    }

    @Override
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "prune";
    }

}
