/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.MutableState;
import org.jspecify.annotations.NonNull;


/**
 * Feature for invoking a term feature recursively on all subterms of a term. The result will be the
 * sum of the individual results for subterms. The feature descends to subterms as long as
 * <code>cond</code> returns zero.
 */
public class RecSubTermFeature implements TermFeature {

    private final TermFeature cond, summand;

    private RecSubTermFeature(TermFeature cond, TermFeature summand) {
        this.cond = cond;
        this.summand = summand;
    }

    public static @NonNull TermFeature create(TermFeature cond, TermFeature summand) {
        return new RecSubTermFeature(cond, summand);
    }

    public RuleAppCost compute(@NonNull Term term, MutableState mState, Services services) {
        RuleAppCost res = summand.compute(term, mState, services);

        if (res instanceof TopRuleAppCost
                || cond.compute(term, mState, services) instanceof TopRuleAppCost) {
            return res;
        }

        for (int i = 0; i != term.arity() && !(res instanceof TopRuleAppCost); ++i) {
            res = res.add(compute(term.sub(i), mState, services));
        }

        return res;
    }
}
