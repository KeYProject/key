// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureSimplify;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory;

/**
 * Invokes the ESC Simplify to solve an integer problem. 
 */
public class SimplifyIntegerRule extends AbstractIntegerRule {

    public SimplifyIntegerRule(DecisionProcedureTranslationFactory dptf) {
		this(true, dptf);
    }

    public SimplifyIntegerRule(boolean resultWindow, 
			       DecisionProcedureTranslationFactory dptf) {
    	super(new Name("Decision Procedure Simplify"), resultWindow, dptf);
    }
    
    protected AbstractDecisionProcedure getDecisionProcedure ( Goal goal,
            Constraint userConstraint, Services services) {
        return new DecisionProcedureSimplify ( goal, userConstraint, this.dptf, services );
    }

    public AbstractIntegerRule clone(DecisionProcedureTranslationFactory dptf) {        
        return new SimplifyIntegerRule(showResults, dptf);
    }
}
