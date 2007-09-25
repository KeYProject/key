// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
 * Implementors will know whether to create a DecProcTranslation object for Java
 * or for ASM. This is necessary since the Translation classes are not visible
 * to callers of the DecisionProcedure classes.
 * 
 * @author daniels
 */
public interface DecisionProcedureTranslationFactory {
	SimplifyTranslation createSimplifyTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services, boolean lightWeight)
			throws SimplifyException;
	ICSTranslation createICSTranslation(Sequent sequent, ConstraintSet cs,
			SetOfMetavariable localmv, Services services) throws SimplifyException;
    
    SmtAufliaTranslation createSmtAufliaTranslation( Sequent sequent, Services services, 
                                                     boolean useQuantifiers );
}
