/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model.builtin;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.LoopContractInternalBuiltInRuleApp;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class LoopContractInternalBuiltInRuleInteraction extends BuiltInRuleInteraction {
    private static final long serialVersionUID = 1L;

    public LoopContractInternalBuiltInRuleInteraction() {
    }

    public LoopContractInternalBuiltInRuleInteraction(LoopContractInternalBuiltInRuleApp app,
            Node node) {
    }
}
