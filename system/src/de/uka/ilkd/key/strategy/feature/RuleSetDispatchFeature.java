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



package de.uka.ilkd.key.strategy.feature;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;


/**
 * Feature for relating rule sets with feature terms. Given a taclet
 * application, this feature will iterate over the rule sets that the taclet
 * belongs to, and for each rule set the corresponding feature term (if
 * existing) is evaluated. The result of the feature is the sum of the results
 * of the different rule set features.
 */
public class RuleSetDispatchFeature implements Feature {

    private final Map<RuleSet, Feature> rulesetToFeature = new LinkedHashMap<RuleSet, Feature> ();
    
    private RuleSetDispatchFeature() {}
    
    public static RuleSetDispatchFeature create() {
        return new RuleSetDispatchFeature ();
    }
    
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( ! ( app instanceof TacletApp ) ) return LongRuleAppCost.ZERO_COST;

        RuleAppCost res = LongRuleAppCost.ZERO_COST;
        for (RuleSet rs : ( (TacletApp)app ).taclet ().getRuleSets ()) {
            final Feature partialF = rulesetToFeature.get ( rs );
            if ( partialF != null ) {
        	res = res.add ( partialF.compute ( app, pos, goal ) );
                if ( res instanceof TopRuleAppCost ) {
                    break;
                }

            }       
        }
        return res;
    }

    /**
     * Bind feature <code>f</code> to the rule set <code>ruleSet</code>. If
     * this method is called more than once for the same rule set, the given
     * features are added to each other.
     */
    public void add(RuleSet ruleSet, Feature f) {
        Feature combinedF = rulesetToFeature.get ( ruleSet );
        if ( combinedF == null )
            combinedF = f;
        else
            combinedF = BinarySumFeature.createSum ( combinedF, f );

        rulesetToFeature.put ( ruleSet, combinedF );
    }
    
    /**
     * Remove all features that have been related to <code>ruleSet</code>.
     */
    public void clear(RuleSet ruleSet) {
        rulesetToFeature.remove ( ruleSet );
    }
    
    /**
     * Returns the used {@link Feature} for the given {@link RuleSet}.
     * @param ruleSet The {@link RuleSet} to get its {@link Feature}.
     * @return The {@link Feature} used for the given {@link RuleSet} or {@code null} if not available.
     */
    public Feature get(RuleSet ruleSet) {
       return rulesetToFeature.get(ruleSet);
    }
}
