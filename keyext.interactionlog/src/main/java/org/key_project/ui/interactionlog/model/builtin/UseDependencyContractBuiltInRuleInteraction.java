package org.key_project.ui.interactionlog.model.builtin;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.UseDependencyContractApp;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class UseDependencyContractBuiltInRuleInteraction extends BuiltInRuleInteraction {
    private static final long serialVersionUID = 1L;

    public UseDependencyContractBuiltInRuleInteraction() {
    }

    public UseDependencyContractBuiltInRuleInteraction(UseDependencyContractApp app, Node node) {
    }
}
