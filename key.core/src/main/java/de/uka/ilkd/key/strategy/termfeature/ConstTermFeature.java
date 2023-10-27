/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A feature that returns a constant value
 */
public class ConstTermFeature implements TermFeature {
    public RuleAppCost compute(Term term, Services services) {
        return val;
    }

    private ConstTermFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static TermFeature createConst(RuleAppCost p_val) {
        return new ConstTermFeature(p_val);
    }

    private final RuleAppCost val;
}
