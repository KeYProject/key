package de.uka.ilkd.key.gui.interactionlog.model.builtin;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.interactionlog.model.NodeInteraction;
import de.uka.ilkd.key.gui.interactionlog.model.OccurenceIdentifier;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public abstract class BuiltInRuleInteraction extends NodeInteraction {
    private String ruleName;

    public BuiltInRuleInteraction() {
    }

    public String getRuleName() {
        return ruleName;
    }

    public void setRuleName(String ruleName) {
        this.ruleName = ruleName;
    }
}