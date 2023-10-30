/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Abstract superclass for features that have either zero cost or top cost.
 */
public abstract class BinaryTermFeature implements TermFeature {

    protected BinaryTermFeature() {}

    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    final public RuleAppCost compute(Term term, Services services) {
        return filter(term, services) ? ZERO_COST : TOP_COST;
    }

    protected abstract boolean filter(Term term, Services services);

}
