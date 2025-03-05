/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

public class PrintTermFeature implements TermFeature {

    public static final TermFeature INSTANCE = new PrintTermFeature();

    private PrintTermFeature() {}

    public RuleAppCost compute(Term term, MutableState mState, LogicServices services) {
        return NumberRuleAppCost.getZeroCost();
    }
}
