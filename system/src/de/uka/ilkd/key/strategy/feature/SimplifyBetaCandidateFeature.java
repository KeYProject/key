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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns zero iff the hyper-tableaux simplification method
 * approves the given application (which is supposed to be the application of a
 * beta rule). Used terminology is defined in Diss. by Martin Giese.
 */
public class SimplifyBetaCandidateFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new SimplifyBetaCandidateFeature ();
    
    private SimplifyBetaCandidateFeature () {}
    
    protected RuleAppCost doComputation (PosInOccurrence pos, Term findTerm) {
        return isBetaCandidate ( findTerm, pos.isInAntec () )
                           ? BinaryFeature.ZERO_COST
                           : BinaryFeature.TOP_COST;
    }

}
