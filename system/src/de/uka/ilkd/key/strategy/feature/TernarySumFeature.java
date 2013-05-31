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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
* A feature that computes the sum of three given features (faster than the more
* general class <code>SumFeature</code>)
*/
public class TernarySumFeature implements Feature {

    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        RuleAppCost res = f0.compute ( app, pos, goal );
        if ( res instanceof TopRuleAppCost ) return res;
        res = res.add ( f1.compute ( app, pos, goal ) );
        if ( res instanceof TopRuleAppCost ) return res;
        return res.add ( f2.compute ( app, pos, goal ) );
    }

    private TernarySumFeature(Feature f0, Feature f1, Feature f2) {
        this.f0 = f0;
        this.f1 = f1;
        this.f2 = f2;
    }

    public static Feature createSum(Feature f0, Feature f1, Feature f2) {
        return new TernarySumFeature ( f0, f1, f2 );
    }

    private final Feature f0, f1, f2;
    
}
