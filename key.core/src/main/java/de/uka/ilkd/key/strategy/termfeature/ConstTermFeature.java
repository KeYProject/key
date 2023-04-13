package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * A feature that returns a constant value
 */
public class ConstTermFeature implements TermFeature {
    public long compute(Term term, Services services) {
        return val;
    }

    private ConstTermFeature(long p_val) {
        val = p_val;
    }

    public static TermFeature createConst(long p_val) {
        return new ConstTermFeature(p_val);
    }

    private final long val;
}
