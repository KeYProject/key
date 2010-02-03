// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.decproc;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;

/**
 * Returns the Translation classes for Java.
 * @author daniels
 */
public class JavaDecisionProcedureTranslationFactory
		implements
			DecisionProcedureTranslationFactory {
    
	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createSimplifyTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
	 */
	public SimplifyTranslation createSimplifyTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services, boolean lightWeight)
			throws SimplifyException {
		return new SimplifyTranslation(sequent, cs, localmv, services,
					       lightWeight);
	}
    
	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createICSTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
	 */
	public ICSTranslation createICSTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services)
			throws SimplifyException {
		return new ICSTranslation(sequent, cs, localmv, services);	
	}
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createSmtTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
     */
    public SmtAufliaTranslation createSmtAufliaTranslation( Sequent sequent, Services services, 
                                                            boolean useQuantifiers ) {            
        return new SmtAufliaTranslation( sequent, services, useQuantifiers );  
    }
}
