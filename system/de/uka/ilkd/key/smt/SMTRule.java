//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.IOException;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

public class SMTRule implements BuiltInRule {

    private final SMTSolver solver;

    
    public SMTRule(SMTSolver arg1) {
	this.solver = arg1;
    }

    /**
     * This rule's name.
     */
    public String displayName() {
	return solver.name();
    }

    /**
     * This rule's name as Name object.
     */
    public Name name() {
	return new Name(displayName());
    }

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
	int timeout = ProofSettings.DEFAULT_SETTINGS
	                           .getDecisionProcedureSettings()
	                           .getTimeout();
	
	SMTSolverResult result = SMTSolverResult.NO_IDEA;	
	try {
	    result = this.solver.run(goal, timeout, services);
	} catch (IOException ioe) {	    	    
	    if (services.getExceptionHandler() != null) {
		services.getExceptionHandler().reportException(ioe);
	    } else {
		RuntimeException re = new RuntimeException(ioe.getMessage());
		re.initCause(ioe);
		throw re;
	    }	    
	}
	if (result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) {
	    return SLListOfGoal.EMPTY_LIST;
	} else {
	    return null;
	}
    }
    
    public String toString() {
	return name().toString();
    }
}
