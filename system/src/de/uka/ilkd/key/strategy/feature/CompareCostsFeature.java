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
import de.uka.ilkd.key.rule.RuleApp;

public abstract class CompareCostsFeature extends BinaryFeature {

    protected final Feature a, b;
    
    private CompareCostsFeature(Feature a, Feature b) {
        this.a = a;
        this.b = b;
    }

    public static Feature less (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).compareTo (
                       b.compute ( app, pos, goal ) ) < 0;
            }            
        };
    }
    
    public static Feature leq (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).compareTo (
                       b.compute ( app, pos, goal ) ) <= 0;
            }            
        };
    }
    
    public static Feature eq (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).equals (
                       b.compute ( app, pos, goal ) );
            }            
        };
    }
    
}