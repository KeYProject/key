/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

/// A feature that computes the sum of two given features (faster than the more general class
/// <code>SumFeature</code>)
public class BinarySumTermFeature implements TermFeature {

    public RuleAppCost compute(Term term, MutableState mState, LogicServices services) {
        RuleAppCost f0Cost = f0.compute(term, mState, services);
        if (f0Cost instanceof TopRuleAppCost) {
            return f0Cost;
        }
        return f0Cost.add(f1.compute(term, mState, services));
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
