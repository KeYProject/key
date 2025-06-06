/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

/// Abstract superclass for features that have either zero cost or top cost.
public abstract class BinaryTermFeature implements TermFeature {

    protected BinaryTermFeature() {}

    /// Constant that represents the boolean value true
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /// Constant that represents the boolean value false
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    final public RuleAppCost compute(Term term, MutableState mState, LogicServices services) {
        return filter(term, mState, services) ? ZERO_COST : TOP_COST;
    }

    protected abstract boolean filter(Term term, MutableState mState, LogicServices services);

}
