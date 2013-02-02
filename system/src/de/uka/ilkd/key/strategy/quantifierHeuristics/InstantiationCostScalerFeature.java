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



package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class InstantiationCostScalerFeature implements Feature {

    private final Feature costFeature;
    private final Feature allowSplitting;
    
    private static final RuleAppCost ONE_COST =
        LongRuleAppCost.create ( 1 );
    private static final RuleAppCost MINUS_3000_COST =
        LongRuleAppCost.create ( -3000 );

    private InstantiationCostScalerFeature(Feature costFeature,
                                           Feature allowSplitting) {
        this.costFeature = costFeature;
        this.allowSplitting = allowSplitting;
    }
    
    public static Feature create(Feature costFeature,
                                 Feature allowSplitting) {
        return new InstantiationCostScalerFeature ( costFeature, allowSplitting );
    }

    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        
        final RuleAppCost cost = costFeature.compute ( app, pos, goal );
        
        if ( cost.equals ( LongRuleAppCost.ZERO_COST ) ) return MINUS_3000_COST;
        if ( cost.equals ( ONE_COST ) ) return LongRuleAppCost.ZERO_COST;
        
        final RuleAppCost as = allowSplitting.compute ( app, pos, goal );
        if ( !as.equals ( LongRuleAppCost.ZERO_COST ) ) return TopRuleAppCost.INSTANCE;
        
        assert cost instanceof LongRuleAppCost : "Can only handle LongRuleAppCost";
        
        final LongRuleAppCost longCost = (LongRuleAppCost)cost;
        return LongRuleAppCost.create ( longCost.getValue () + 200 );
    }
    
}
