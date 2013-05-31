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
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/**
 * Binary feature that returns zero iff the replacewith- and find-parts 
 * of a Taclet are matched to different terms.
 */
public class DiffFindAndReplacewithFeature extends BinaryTacletAppFeature {
    
    /** the single instance of this feature */
    public static final Feature INSTANCE = new DiffFindAndReplacewithFeature ();

    private DiffFindAndReplacewithFeature () {}
    
    protected boolean filter ( TacletApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null && app.rule() instanceof RewriteTaclet 
               : "Feature is only applicable to rewrite taclets";
        
        for(TacletGoalTemplate temp : ((Taclet)app.rule()).goalTemplates()) {
            RewriteTacletGoalTemplate rwtemp = (RewriteTacletGoalTemplate) temp;
            if(rwtemp.replaceWith().equals(pos.subTerm())) {
        	return false;
            }
        }
        return true;
    }
}
