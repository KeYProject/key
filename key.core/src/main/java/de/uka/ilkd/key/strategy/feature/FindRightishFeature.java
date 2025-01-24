/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * Walking from the root of a formula down to the focus of a rule application, count how often we
 * choose the left branch (subterm) and how the right branches. This is used to identify the
 * upper/righter/bigger summands in a polynomial that is arranged in a left-associated way.
 */
public class FindRightishFeature implements Feature<Goal> {
    private final Operator add;
    private final static RuleAppCost one = NumberRuleAppCost.create(1);

    public static Feature<Goal> create(IntegerLDT numbers) {
        return new FindRightishFeature(numbers);
    }

    private FindRightishFeature(IntegerLDT numbers) {
        add = numbers.getAdd();
    }

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final var op = it.getSubTerm().op();
            final int index = it.getChild();
            if (index == 0 && op == add || index == 1 && op == Equality.EQUALS) {
                res = res.add(one);
            }
        }

        return res;
    }


}
