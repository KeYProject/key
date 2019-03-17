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

/**
 * Projection of a rule application to its focus (the term or formula that the
 * rule operates on, that for taclets is described using <code>\find</code>,
 * and that can be modified by the rule). Optionally, the projection can walk
 * "upwards" towards the root of the term/formula
 */
public class FocusProjection implements ProjectionToTerm {

    public static final ProjectionToTerm INSTANCE = create(0);

    private final int stepsUpwards;
    
    private FocusProjection(int stepsUpwards) {
       assert stepsUpwards >= 0;
        this.stepsUpwards = stepsUpwards;
    }

    public static ProjectionToTerm create(int stepsUpwards) {
        return new FocusProjection ( stepsUpwards );
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Projection is only applicable to rules with find";

        int n = stepsUpwards;
        while ( n-- > 0 && !pos.isTopLevel() ) {
            pos = pos.up ();
        }
        
        return pos.subTerm ();
    }
    
}