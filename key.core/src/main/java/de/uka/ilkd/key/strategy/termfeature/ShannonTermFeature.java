/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.MutableState;

/**
 * A conditional feature, in which the condition itself is a (binary) feature. The general notion is
 * a term <code>c ? f1 : f2</code>, whereby the condition <code>c</code> determines whether the
 * value of the whole expression is <code>f1</code> (if <code>c</code> returns zero, or more general
 * if <code>c</code> returns a distinguished value <code>trueCost</code>) or <code>f2</code>
 */
public class ShannonTermFeature implements TermFeature {

    /**
     * The filter that decides which sub-feature is to be evaluated
     */
    private final TermFeature cond;

    /**
     * If the result of <code>cond</code> is this cost, then the condition is assumed to hold
     */
    private final RuleAppCost trueCost;

    /**
     * The feature for positive results of <code>filter</code>
     */
    private final TermFeature thenFeature;

    /**
     * The feature for negative results of <code>filter</code>
     */
    private final TermFeature elseFeature;

    private ShannonTermFeature(TermFeature p_cond, RuleAppCost p_trueCost,
            TermFeature p_thenFeature, TermFeature p_elseFeature) {
        cond = p_cond;
        trueCost = p_trueCost;
        thenFeature = p_thenFeature;
        elseFeature = p_elseFeature;
    }

    public RuleAppCost compute(Term term, MutableState mState, Services services) {
        if (cond.compute(term, mState, services).equals(trueCost)) {
            return thenFeature.compute(term, mState, services);
        } else {
            return elseFeature.compute(term, mState, services);
        }
    }

    /**
     * @param cond the feature that decides which value is to be returned
     * @param thenFeature the value of the feature if <code>cond</code> returns zero
     * @param elseFeature the value of the feature if <code>cond</code> does not return zero
     * @return the value of <code>thenFeature</code> if <code>cond</code> returns zero, the value of
     *         <code>elseFeature</code> otherwise
     */
    public static TermFeature createConditionalBinary(TermFeature cond, TermFeature thenFeature,
            TermFeature elseFeature) {
        return new ShannonTermFeature(cond, BinaryTermFeature.ZERO_COST, thenFeature, elseFeature);
    }

    /**
     * @param cond the feature that decides which value is to be returned
     * @param thenFeature the value of the feature if <code>cond</code> returns zero
     * @return the value of <code>thenFeature</code> if <code>cond</code> returns zero, zero
     *         otherwise
     */
    public static TermFeature createConditionalBinary(TermFeature cond, TermFeature thenFeature) {
        return createConditionalBinary(cond, thenFeature,
            ConstTermFeature.createConst(NumberRuleAppCost.getZeroCost()));
    }

}
