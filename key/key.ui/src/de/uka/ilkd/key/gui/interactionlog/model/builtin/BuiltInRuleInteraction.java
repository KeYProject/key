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


    @Override
    public String getProofScriptRepresentation(Services services) {
        return ruleName + ";";
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
                .append("------\n")
                .append("## BuiltInRuleInteraction ")
                .append(ruleName)
                .append("\n\n")
                .append("### PosInOccurence\n")
                .append("```\n")
                //.append(pos)
                .append("\n```\n\n");

        return sb.toString();
    }

    public String getRuleName() {
        return ruleName;
    }

    public void setRuleName(String ruleName) {
        this.ruleName = ruleName;
    }
}