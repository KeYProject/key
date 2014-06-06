// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A feature that evaluates one of two given features, depending on the result
 * of a <code>RuleFilter</code>
 */
public class ConditionalFeature implements Feature {
    
    private ConditionalFeature (RuleFilter p_cond,
                                Feature    p_thenFeature,
                                Feature    p_elseFeature) {
        cond        = p_cond;
        thenFeature = p_thenFeature;
        elseFeature = p_elseFeature;
    }
    
    public RuleAppCost compute (RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( cond.filter ( app.rule() ) )
            return thenFeature.compute ( app, pos, goal );
        else
            return elseFeature.compute ( app, pos, goal );
    }

    /**
     * @param cond the filter that decides which value is to be returned
     * @param thenValue the value of the feature, if <code>filter</code>
     * returns true
     */
    public static Feature createConditional (RuleFilter  cond,
                                             RuleAppCost thenValue) {
        return createConditional ( cond,
                                   ConstFeature.createConst ( thenValue ) );
    }

    /**
     * @param cond the filter that decides which value is to be returned
     * @param thenValue the value of the feature, if <code>filter</code>
     * returns true
     * @param elseValue the value of the feature, if <code>filter</code>
     * returns false
     */
    public static Feature createConditional (RuleFilter  cond,
                                             RuleAppCost thenValue,
                                             RuleAppCost elseValue) {
        return createConditional ( cond,
                                   ConstFeature.createConst ( thenValue ),
                                   ConstFeature.createConst ( elseValue ) );
    }

    /**
     * @param cond the filter that decides which value is to be returned
     * @param thenFeature the feature that is evaluted, if <code>filter</code>
     * returns true
     * returns false
     */
    public static Feature createConditional (RuleFilter cond,
            				     Feature    thenFeature) {
        return createConditional ( cond,
                                   thenFeature,
                                   NumberRuleAppCost.getZeroCost() );
    }

    /**
     * @param cond the filter that decides which value is to be returned
     * @param thenFeature the feature that is evaluted, if <code>filter</code>
     * returns true
     * @param elseValue the value of the feature, if <code>filter</code>
     * returns false
     */
    public static Feature createConditional (RuleFilter  cond,
                                             Feature     thenFeature,
                                             RuleAppCost elseValue) {
        return createConditional ( cond,
                                   thenFeature,
                                   ConstFeature.createConst ( elseValue ) );
    }

    /**
     * @param cond the filter that decides which value is to be returned
     * @param thenFeature the feature that is evaluted, if <code>filter</code>
     * returns true
     * @param elseFeature the feature that is evaluted, if <code>filter</code>
     * returns false
     */
    public static Feature createConditional (RuleFilter cond,
                                             Feature    thenFeature,
                                             Feature    elseFeature) {
        return new ConditionalFeature ( cond, thenFeature, elseFeature );
    }

    /**
     * The filter that decides which sub-feature is to be evaluated
     */
    private final RuleFilter cond;

    /**
     * The feature for positive results of <code>filter</code>
     */
    private final Feature    thenFeature;

    /**
     * The feature for negative results of <code>filter</code>
     */
    private final Feature    elseFeature;
}