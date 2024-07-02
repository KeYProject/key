package org.key_project.ui.interactionlog.model.builtin;

import org.key_project.ui.interactionlog.model.NodeInteraction;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlTransient;

@XmlTransient
@XmlAccessorType(XmlAccessType.FIELD)
public abstract class BuiltInRuleInteraction extends NodeInteraction {
    private static final long serialVersionUID = -4704080776691885200L;

    @XmlAttribute
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