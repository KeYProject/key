// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A conditional feature, in which the condition itself is a (binary) feature.
 * The general notion is a term <code>c ? f1 : f2</code>, whereby the
 * condition <code>c</code> determines whether the value of the whole
 * expression is <code>f1</code> (if <code>c</code> returns zero, or more
 * general if <code>c</code> returns a distinguished value
 * <code>trueCost</code>) or <code>f2</code>
 */
public class ShannonTermFeature implements TermFeature {

    /**
     * The filter that decides which sub-feature is to be evaluated
     */
    private final TermFeature cond;

    /**
     * If the result of <code>cond</code> is this cost, then the condition is
     * assumed to hold
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

    private ShannonTermFeature(TermFeature p_cond,
                               RuleAppCost p_trueCost,
                               TermFeature p_thenFeature,
                               TermFeature p_elseFeature) {
        cond = p_cond;
        trueCost = p_trueCost;
        thenFeature = p_thenFeature;
        elseFeature = p_elseFeature;
    }

    public RuleAppCost compute(Term term, Services services) {
        if ( cond.compute ( term, services ).equals ( trueCost ) )
            return thenFeature.compute ( term, services );
        else
            return elseFeature.compute ( term, services );
    }

    /**
     * @param cond
     *            the feature that decides which value is to be returned
     * @param thenFeature
     *            the value of the feature if <code>cond</code> returns zero
     * @param elseFeature
     *            the value of the feature if <code>cond</code> does not
     *            return zero
     * @return the value of <code>thenFeature</code> if <code>cond</code>
     *         returns zero, the value of <code>elseFeature</code> otherwise
     */
    public static TermFeature createConditionalBinary(TermFeature cond,
                                                      TermFeature thenFeature,
                                                      TermFeature elseFeature) {
        return new ShannonTermFeature ( cond,
                                        BinaryTermFeature.ZERO_COST,
                                        thenFeature,
                                        elseFeature );
    }

    /**
     * @param cond
     *            the feature that decides which value is to be returned
     * @param thenFeature
     *            the value of the feature if <code>cond</code> returns zero
     * @return the value of <code>thenFeature</code> if <code>cond</code>
     *         returns zero, zero otherwise
     */
    public static TermFeature createConditionalBinary (TermFeature cond,
                                                       TermFeature thenFeature) {
        return createConditionalBinary ( cond,
                                         thenFeature,
                                         ConstTermFeature.createConst
                                         	(NumberRuleAppCost.getZeroCost()) );
    }

}
