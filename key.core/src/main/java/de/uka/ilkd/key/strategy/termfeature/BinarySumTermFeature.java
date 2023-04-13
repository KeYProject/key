package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A feature that computes the sum of two given features (faster than the more general class
 * <code>SumFeature</code>)
 */
public class BinarySumTermFeature implements TermFeature {

    public long compute(Term term, Services services) {
        var a = f0.compute(term, services);
        if (a == RuleAppCost.MAX_VALUE) {
            return a;
        }
        return RuleAppCost.addRight(f1.compute(term, services), a);
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
