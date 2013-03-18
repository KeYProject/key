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



package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Projection for computing a subterm of a given term. The position of the
 * subterm within the complete term is described using a <code>PosInTerm</code>.
 */
public class SubtermProjection implements ProjectionToTerm {

    private final PosInTerm pit;
    private final ProjectionToTerm completeTerm;

    public static ProjectionToTerm create(ProjectionToTerm completeTerm,
                                          PosInTerm pit) {
        return new SubtermProjection ( completeTerm, pit );
    }

    private SubtermProjection(ProjectionToTerm completeTerm, PosInTerm pit) {
        this.completeTerm = completeTerm;
        this.pit = pit;
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        return completeTerm.toTerm ( app, pos, goal ).subAt ( pit );
    }
}
