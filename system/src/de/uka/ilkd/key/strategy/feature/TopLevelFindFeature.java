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

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Feature for investigating whether the focus of a rule application is a
 * top-level formula, a top-level formula of the antecedent or a top-level
 * formula of the succedent
 */
public abstract class TopLevelFindFeature extends BinaryTacletAppFeature {

    private static abstract class TopLevelWithoutUpdate extends TopLevelFindFeature {
        protected abstract boolean matches(PosInOccurrence pos);
        
        protected boolean checkPosition(PosInOccurrence pos) {
            return pos.isTopLevel () && matches ( pos );
        }
    }
    
    private static abstract class TopLevelWithUpdate extends TopLevelFindFeature {
        protected abstract boolean matches(PosInOccurrence pos);
        
        protected boolean checkPosition(PosInOccurrence pos) {
            if ( !pos.isTopLevel () ) {
                final PIOPathIterator it = pos.iterator ();
                while ( it.next () != -1 ) {
                    if ( ! ( it.getSubTerm ().op () instanceof UpdateApplication ) )
                        return false;
                }
            }
            
            return matches ( pos );
        }
    }
    
    public final static Feature ANTEC_OR_SUCC =
        new TopLevelWithoutUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return true;
        }
    };
    
    public final static Feature ANTEC =
        new TopLevelWithoutUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return pos.isInAntec ();
        }
    };
    
    public final static Feature SUCC =
        new TopLevelWithoutUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return !pos.isInAntec ();
        }
    };
    
    public final static Feature ANTEC_OR_SUCC_WITH_UPDATE =
        new TopLevelWithUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return true;
        }
    };
    
    public final static Feature ANTEC_WITH_UPDATE =
        new TopLevelWithUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return pos.isInAntec ();
        }
    };
    
    public final static Feature SUCC_WITH_UPDATE =
        new TopLevelWithUpdate () {
            protected boolean matches(PosInOccurrence pos) {
                return !pos.isInAntec ();
        }
    };
    
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        return checkPosition ( pos );
    }

    protected abstract boolean checkPosition(PosInOccurrence pos);
    
}