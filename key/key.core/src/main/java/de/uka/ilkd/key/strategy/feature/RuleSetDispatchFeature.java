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

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
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

    private final Map<RuleSet, Feature> rulesetToFeature = new LinkedHashMap<> ();
    
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( ! ( app instanceof TacletApp ) ) return NumberRuleAppCost.getZeroCost();

        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        ImmutableList<RuleSet> ruleSetsOfAppliedTaclet = ( (TacletApp)app ).taclet ().getRuleSets ();
        /*
         * do not use iterator here, as this method is called a lot when proving such that avoiding
         * object creation helps to reduce the load put on the garbage collector
         */
        while (!ruleSetsOfAppliedTaclet.isEmpty()) {
        	final RuleSet rs = ruleSetsOfAppliedTaclet.head();
        	ruleSetsOfAppliedTaclet = ruleSetsOfAppliedTaclet.tail();
            
        	final Feature partialF = rulesetToFeature.get ( rs );
            if ( partialF != null ) {
                res = res.add (partialF.computeCost ( app, pos, goal ) );
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
            combinedF = SumFeature.createSum ( combinedF, f );

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
