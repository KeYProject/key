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


/// Feature for invoking a list of term features on the direct subterms of a given term. The result
/// will be the sum of the individual results. If the arity of the term investigated does not
/// coincide with the number of term features that are given as arguments,
/// <code>arityMismatchCost</code> will be returned
public class SubTermFeature implements TermFeature {

    private SubTermFeature(TermFeature[] features, RuleAppCost arityMismatchCost) {
        this.features = features;
        this.arityMismatchCost = arityMismatchCost;
    }

    public static TermFeature create(TermFeature[] fs, RuleAppCost arityMismatchCost) {
        final TermFeature[] fsCopy = new TermFeature[fs.length];
        System.arraycopy(fs, 0, fsCopy, 0, fs.length);
        return new SubTermFeature(fsCopy, arityMismatchCost);
    }

    public static TermFeature create(TermFeature[] fs) {
        return create(fs, TopRuleAppCost.INSTANCE);
    }

    private final TermFeature[] features;
    private final RuleAppCost arityMismatchCost;

    public RuleAppCost compute(Term term, MutableState mState, LogicServices services) {
        if (term.arity() != features.length) {
            return arityMismatchCost;
        }

        RuleAppCost res = NumberRuleAppCost.getZeroCost();

        for (int i = 0; i < features.length && !(res instanceof TopRuleAppCost); i++) {
            res = res.add(features[i].compute(term.sub(i), mState, services));
        }

        return res;
    }
}
