// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof.decproc;

import de.uka.ilkd.asmkey.logic.AsmOperator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
import de.uka.ilkd.key.proof.decproc.SimplifyException;
import de.uka.ilkd.key.proof.decproc.SimplifyTranslation;

public class AsmSimplifyTranslation extends SimplifyTranslation {
    AsmSimplifyTranslation(Sequent sequent, ConstraintSet cs, 
			SetOfMetavariable localmv, Services services) throws SimplifyException  {
    	super(sequent, cs, localmv, services);
    }

    /**
     * Handles AsmOperator which SimplifyTranslation doesn't know.
     * @param term The Term given to translate
     * @throws SimplifyException
     */
    protected StringBuffer translateUnknown(Term term) throws SimplifyException {
    	if (term.op() instanceof AsmOperator) {
    	    return(uninterpretedTerm(term, true));
    	} else {
    		return(opNotKnownWarning(term));
    	}
    }
    
}
