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
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

public class TriggerVarInstantiatedFeature extends  BinaryTacletAppFeature {

    public static Feature INSTANCE  = new TriggerVarInstantiatedFeature();
    
    private TriggerVarInstantiatedFeature() {
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert app.taclet().hasTrigger();
        
         SVInstantiationProjection instProj = 
                 SVInstantiationProjection.create(app.taclet().getTrigger().getTriggerVar().name(), false );

        return instProj.toTerm ( app, pos, goal ) != null;
    }

    
}