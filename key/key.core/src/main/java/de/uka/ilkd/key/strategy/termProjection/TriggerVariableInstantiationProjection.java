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

package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;

public class TriggerVariableInstantiationProjection implements ProjectionToTerm  {

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert app.rule() instanceof Taclet;
        final Taclet t = (Taclet) app.rule();
        
        final SVInstantiationProjection instProj = 
                SVInstantiationProjection.create(t.getTrigger().getTriggerVar().name(),
                true);
        return instProj.toTerm(app, pos, goal);
    }

    
    
}