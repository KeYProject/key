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

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Feature that returns zero iff the application focus of a rule is a potential
 * cut position (taclet cut_direct). For positions that are below quantifiers,
 * the feature generally returns zero.
 */
public class AllowedCutPositionFeature extends BinaryFeature {

    public static final Feature INSTANCE = new AllowedCutPositionFeature ();

    private AllowedCutPositionFeature () {}
    
    public boolean filter (RuleApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse ( pos == null,
                            "Feature is only applicable to rules with find" );

        return onlyBelowRightJunctors ( pos );
    }

    private boolean onlyBelowRightJunctors (PosInOccurrence pos) {
        boolean negated = pos.isInAntec ();        
        final PIOPathIterator it = pos.iterator ();

        while ( it.next () != -1 ) {
            final int child = it.getChild ();
            final Operator op = it.getSubTerm ().op ();
            
            if ( op == Junctor.NOT ) {
                negated = !negated;
            } else if ( op == ( negated ? Junctor.OR : Junctor.AND ) ) {
                /* nothing */
            } else if ( negated && op == Junctor.IMP ) {
                if ( child == 0 ) negated = !negated;
            } else {
                return op instanceof Quantifier;
            }
        }
        
        return true;
    }

}
