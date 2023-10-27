/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;


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

    public static TermFeature create(TermFeature cond, TermFeature summand) {
        return new RecSubTermFeature(cond, summand);
    }

    public RuleAppCost compute(Term term, Services services) {
        RuleAppCost res = summand.compute(term, services);

        if (res instanceof TopRuleAppCost
                || cond.compute(term, services) instanceof TopRuleAppCost) {
            return res;
        }

        for (int i = 0; i != term.arity() && !(res instanceof TopRuleAppCost); ++i) {
            res = res.add(compute(term.sub(i), services));
        }

        return res;
    }
}
