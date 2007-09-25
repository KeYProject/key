// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
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

    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    protected boolean lessThan(Term t1, Term t2) {
        
        final Sort sort1 = t1.sort ();
        final Sort sort2 = t2.sort ();
        if ( !sort1.equals ( sort2 ) ) {
            if ( sort1.extendsTrans ( sort2 ) ) return true;
            if ( sort2.extendsTrans ( sort1 ) ) return false;
        }
        
        return super.lessThan ( t1, t2 );
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return lessThan ( left.toTerm ( app, pos, goal ),
                          right.toTerm ( app, pos, goal ) );
    }

}
