// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.util.Debug;


/**
 *
 */
public class QuanAssignmentPairLazy extends AbstractAssignmentPairLazy {
    
    public QuanAssignmentPairLazy (Term update, int locationPos) {
        super ( update, locationPos );
        Debug.assertTrue ( getUpdateOp () instanceof QuanUpdateOperator );
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#boundVars()
     */
    public ArrayOfQuantifiableVariable boundVars () {
        return getQuanUpdateOp ().boundVars ( getUpdateTerm (),
                                              getLocationPos () );
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#guard()
     */
    public Term guard () {
        return getQuanUpdateOp ().guard ( getUpdateTerm (), getLocationPos () );
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#nontrivialGuard()
     */
    public boolean nontrivialGuard () {
        return guard ().op () != Op.TRUE;
    }

    private QuanUpdateOperator getQuanUpdateOp () {
        return (QuanUpdateOperator)getUpdateOp ();
    }

}
