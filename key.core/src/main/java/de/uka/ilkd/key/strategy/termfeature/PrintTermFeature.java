/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

public class PrintTermFeature implements TermFeature {

    public static final TermFeature INSTANCE = new PrintTermFeature();

    private PrintTermFeature() {}

    public RuleAppCost compute(Term term, Services services) {
        return NumberRuleAppCost.getZeroCost();
    }
}
