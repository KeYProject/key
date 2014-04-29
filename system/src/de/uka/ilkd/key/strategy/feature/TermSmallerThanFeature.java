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
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Feature that returns zero iff one term is smaller than another term in the
 * current term ordering
 */
public class TermSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;

    public static Feature create(ProjectionToTerm left, ProjectionToTerm right) {
        return new TermSmallerThanFeature ( left, right );
    }
    
    private TermSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right) {
        this.left = left;
        this.right = right;
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return lessThan ( left.toTerm ( app, pos, goal ),
                          right.toTerm ( app, pos, goal ), goal.proof().getServices().getCaches() );
    }

}