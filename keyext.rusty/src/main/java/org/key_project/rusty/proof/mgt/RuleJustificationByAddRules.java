/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.mgt;

import org.key_project.prover.rules.RuleApp;
import org.key_project.rusty.pp.LogicPrinter;
import org.key_project.rusty.pp.NotationInfo;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.rule.Taclet;

// spotless:off
public record RuleJustificationByAddRules(Node node, boolean isAxiom) implements RuleJustification {
    public RuleJustificationByAddRules {
        assert node != null;
    }

    public boolean isAxiomJustification() {
        return isAxiom;
    }

    public RuleApp motherTaclet() {
        return node.getAppliedRuleApp();
    }

    public String toString() {
        String mother;
        if (motherTaclet().rule() instanceof Taclet tac) {
            LogicPrinter tacPrinter = LogicPrinter.purePrinter(new NotationInfo(), node.proof().getServices());
            tacPrinter.printTaclet(tac);
            mother = tacPrinter.result();
        } else {
            mother = motherTaclet().rule().name().toString();
        }
        return "added rule justification\nintroduced at node " + node.getSerialNr() + " by rule\n" + mother;
    }
}
//spotless:on
