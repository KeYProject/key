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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class ImplicitCastNecessary extends BinaryFeature {

    private final ProjectionToTerm projection;

    private ImplicitCastNecessary(ProjectionToTerm projection) {
        this.projection = projection;       
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null && pos.depth() >= 1;       
        
        int subPos = pos.getIndex();
        
        final Sort maxSort =
            TermHelper.getMaxSort ( pos.up ().subTerm (), 
        	    		    subPos, 
        	    		    goal.proof().getServices() );
        return
          projection.toTerm ( app, pos, goal ).sort ().extendsTrans ( maxSort );
    }

    public static Feature create(ProjectionToTerm s1) {        
        return new ImplicitCastNecessary(s1);
    }

}
