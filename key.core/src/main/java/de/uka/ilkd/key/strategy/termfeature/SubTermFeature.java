package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Feature for invoking a list of term features on the direct subterms of a given term. The result
 * will be the sum of the individual results. If the arity of the term investigated does not
 * coincide with the number of term features that are given as arguments,
 * <code>arityMismatchCost</code> will be returned
 */
public class SubTermFeature implements TermFeature {

    private SubTermFeature(TermFeature[] features, long arityMismatchCost) {
        this.features = features;
        this.arityMismatchCost = arityMismatchCost;
    }

    public static TermFeature create(TermFeature[] fs, long arityMismatchCost) {
        final TermFeature[] fsCopy = new TermFeature[fs.length];
        System.arraycopy(fs, 0, fsCopy, 0, fs.length);
        return new SubTermFeature(fsCopy, arityMismatchCost);
    }

    public static TermFeature create(TermFeature[] fs) {
        return create(fs, RuleAppCost.MAX_VALUE);
    }

    private final TermFeature[] features;
    private final long arityMismatchCost;

    public long compute(Term term, Services services) {
        if (term.arity() != features.length) {
            return arityMismatchCost;
        }

        long res = RuleAppCost.ZERO;

        for (int i = 0; i < features.length; i++) {
            var partial = features[i].compute(term.sub(i), services);
            if (partial == RuleAppCost.MAX_VALUE) {
                return RuleAppCost.MAX_VALUE;
            }
            res = res + partial;
        }

        return res;
    }
}
