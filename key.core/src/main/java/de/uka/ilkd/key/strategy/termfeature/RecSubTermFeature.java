package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


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

    public long compute(Term term, Services services) {
        long res = summand.compute(term, services);

        if (res == RuleAppCost.MAX_VALUE
                || cond.compute(term, services) == RuleAppCost.MAX_VALUE) {
            return res;
        }

        for (int i = 0; i != term.arity(); ++i) {
            var partial = compute(term.sub(i), services);
            if (partial == RuleAppCost.MAX_VALUE) {
                return RuleAppCost.MAX_VALUE;
            }
            res = res + partial;
        }

        return res;
    }
}
