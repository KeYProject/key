/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public record RuleJustificationByAddRules(Node node, boolean isAxiom) implements RuleJustification {

    public RuleJustificationByAddRules {
        assert node != null;
    }

    @Override
    public boolean isAxiomJustification() { return isAxiom; }

    public @Nullable RuleApp motherTaclet() { return node.getAppliedRuleApp(); }

    /**
     * Returns a human-readable description of this rule justification.
     * <p>
     * A rule justification added by a rule always derives from a received rule application; the
     * dereferences of the (nullable) mother rule app are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public String toString() {
        String mother;
        if (motherTaclet().rule() instanceof Taclet) {
            LogicPrinter tacPrinter =
                LogicPrinter.purePrinter(new NotationInfo(), node.proof().getServices());
            tacPrinter.printTaclet((Taclet) (motherTaclet().rule()));
            mother = tacPrinter.result();
        } else {
            mother = motherTaclet().rule().name().toString();
        }
        return "added rule justification \nintroduced at node " + node.serialNr() + " by rule \n"
            + mother;
    }
}
