/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model.builtin;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;

import org.key_project.ui.interactionlog.model.NodeIdentifier;
import org.key_project.ui.interactionlog.model.OccurenceIdentifier;

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */

@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class OSSBuiltInRuleInteraction extends BuiltInRuleInteraction {
    private static final long serialVersionUID = 1L;

    private OccurenceIdentifier occurenceIdentifier;
    private NodeIdentifier nodeIdentifier;

    public OSSBuiltInRuleInteraction() {
    }

    public OSSBuiltInRuleInteraction(OneStepSimplifierRuleApp app, Node node) {
        nodeIdentifier = NodeIdentifier.get(node);
        occurenceIdentifier = OccurenceIdentifier.get(app.posInOccurrence());
    }

    @Override
    public String getMarkdown() {
        return String.format("## One step simplification%n"
            + "* applied on %n  * Term:%s%n  * Toplevel %s%n",
            getOccurenceIdentifier().getTerm(),
            getOccurenceIdentifier().getToplevelTerm());
    }

    @Override
    public String getProofScriptRepresentation() {
        return String.format("one_step_simplify %n" +
            "\t     on = \"%s\"%n" +
            "\tformula = \"%s\"%n;%n",
            getOccurenceIdentifier().getTerm(),
            getOccurenceIdentifier().getToplevelTerm());
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

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        OneStepSimplifier oss = new OneStepSimplifier();
        PosInOccurrence pio = getOccurenceIdentifier().rebuildOn(goal);
        OneStepSimplifierRuleApp app = oss.createApp(pio, goal.proof().getServices());
        goal.apply(app);
    }
}
