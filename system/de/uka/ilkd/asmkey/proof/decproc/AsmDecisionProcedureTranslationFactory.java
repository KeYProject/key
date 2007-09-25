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
/*
 * Created on Jul 28, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package de.uka.ilkd.asmkey.proof.decproc;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SetOfMetavariable;
import de.uka.ilkd.key.proof.decproc.*;

/**
 * @author daniels
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class AsmDecisionProcedureTranslationFactory
		implements
			DecisionProcedureTranslationFactory {
	/**
	 * 
	 */
	public AsmDecisionProcedureTranslationFactory() {
		super();
		// TODO Auto-generated constructor stub
	}
	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createSimplifyTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
	 */
	public SimplifyTranslation createSimplifyTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services)
			throws SimplifyException {
		return new AsmSimplifyTranslation(sequent, cs, localmv, services);
	}

	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createSimplifyTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
	 */
	public SimplifyTranslation createSimplifyTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services, boolean lightWeight)
			throws SimplifyException {
		return new AsmSimplifyTranslation(sequent, cs, localmv, services);
	}

	/* (non-Javadoc)
	 * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory#createICSTranslation(de.uka.ilkd.key.logic.Sequent, de.uka.ilkd.key.proof.decproc.ConstraintSet, de.uka.ilkd.key.logic.op.SetOfMetavariable)
	 */
	public ICSTranslation createICSTranslation(Sequent sequent,
			ConstraintSet cs, SetOfMetavariable localmv, Services services)
			throws SimplifyException {
		return null; //ASM version does not exist yet.
	}


	public SmtAufliaTranslation createSmtAufliaTranslation(Sequent sequent,
			Services services, boolean useQuantifiers ) {
		return null; //ASM version does not exist
	}
}
