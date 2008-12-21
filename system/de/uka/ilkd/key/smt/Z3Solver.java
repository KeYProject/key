package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SetAsListOfMetavariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
import de.uka.ilkd.key.rule.RuleApp;
//import de.uka.ilkd.key.smt.SmtSolver.RESULTTYPE;

public class Z3Solver extends AbstractSmtProver {

    
    @Override
    public String displayName() {
        return "Z3";
    }
    
    @Override
    public Name name() {
	return new Name(this.displayName());
    }
    
    @Override
    protected SmtTranslator getTranslator(Goal goal, Services services, RuleApp ruleApp) {
	return new SmtLibTranslator(goal.sequent(), new ConstraintSet(goal,
		null), SetAsListOfMetavariable.EMPTY_SET, services);
    }
    
    @Override
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[2];

	toReturn[0] = "z3";
	toReturn[1] = "< " + filename;
//	toReturn[2] = "\"" + formula.toString() + "\"";
	
	return toReturn;
    }
    
    @Override
    protected RESULTTYPE answerType(String answer) {
	if (answer.equals("unsat")) {
	    return SmtSolver.RESULTTYPE.VALID;
	} else if (answer.equals("sat")) {
	    return SmtSolver.RESULTTYPE.INVALID;
	} else {
	    return SmtSolver.RESULTTYPE.UNKNOWN;
	}
    }
    
}
