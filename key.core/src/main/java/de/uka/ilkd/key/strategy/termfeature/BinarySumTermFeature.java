/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * A feature that computes the sum of two given features (faster than the more general class
 * <code>SumFeature</code>)
 */
public class BinarySumTermFeature implements TermFeature {

    public RuleAppCost compute(Term term, Services services) {
        RuleAppCost f0Cost = f0.compute(term, services);
        if (f0Cost instanceof TopRuleAppCost) {
            return f0Cost;
        }
        return f0Cost.add(f1.compute(term, services));
    }

    private BinarySumTermFeature(TermFeature f0, TermFeature f1) {
        this.f0 = f0;
        this.f1 = f1;
    }

    public static TermFeature createSum(TermFeature f0, TermFeature f1) {
        return new BinarySumTermFeature(f0, f1);
    }

    private final TermFeature f0, f1;
}
