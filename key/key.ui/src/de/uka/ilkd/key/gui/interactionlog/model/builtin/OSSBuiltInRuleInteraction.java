package de.uka.ilkd.key.gui.interactionlog.model.builtin;

import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;
import de.uka.ilkd.key.gui.interactionlog.model.NodeIdentifier;
import de.uka.ilkd.key.gui.interactionlog.model.OccurenceIdentifier;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */

@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class OSSBuiltInRuleInteraction extends BuiltInRuleInteraction {
    private OccurenceIdentifier occurenceIdentifier;
    private NodeIdentifier nodeIdentifier;

    public OSSBuiltInRuleInteraction() {
    }

    public OSSBuiltInRuleInteraction(OneStepSimplifierRuleApp app, Node node) {
        nodeIdentifier = NodeIdentifier.get(node);
        occurenceIdentifier = OccurenceIdentifier.get(app.posInOccurrence());
    }

    @Override
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "one step simplification on" + occurenceIdentifier.getTerm();
    }

    public OccurenceIdentifier getOccurenceIdentifier() {
        return occurenceIdentifier;
    }

    public void setOccurenceIdentifier(OccurenceIdentifier occurenceIdentifier) {
        this.occurenceIdentifier = occurenceIdentifier;
    }

    public NodeIdentifier getNodeIdentifier() {
        return nodeIdentifier;
    }

    public void setNodeIdentifier(NodeIdentifier nodeIdentifier) {
        this.nodeIdentifier = nodeIdentifier;
    }
}
