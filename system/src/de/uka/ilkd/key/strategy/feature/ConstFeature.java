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

/**
 * A feature that returns a constant value
 */
public class ConstFeature implements Feature {
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        return val;
    }
    
    private ConstFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static Feature createConst(RuleAppCost p_val) {
        return new ConstFeature(p_val);
    }

    private final RuleAppCost val;
}
