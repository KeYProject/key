// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Returns zero iff the position of a rule application is not in the scope of a
 * modal operator (a program block or an update). Note that terms and formulas
 * within (but not behind) updates are not in the scope of the update
 */
public class NotInScopeOfModalityFeature extends BinaryFeature {

    public static final Feature INSTANCE = new NotInScopeOfModalityFeature ();

    private NotInScopeOfModalityFeature () {}
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse ( pos == null,
                            "Feature is only applicable to rules with find" );

        return !inScopeOfModality ( pos );
    }

    private boolean inScopeOfModality (PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator ();

        while ( it.next () != -1 ) {
            final Operator op = it.getSubTerm ().op();
            
            if ( op instanceof Modality ) return true;
            if ( op instanceof IUpdateOperator ) {
                final IUpdateOperator updOp = (IUpdateOperator)op;
                if ( it.getChild () == updOp.targetPos () ) return true;
            }
        }
        
        return false;
    }

}
