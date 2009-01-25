package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SetAsListOfMetavariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class SimplifySolver extends AbstractSmtProver {

    
    @Override
    public String displayName() {
        return "Simplify";
    }
    
    @Override
    protected SmtTranslator getTranslator(Goal goal, Services services, RuleApp rule) {
	return new SimplifyTranslator(goal.sequent(), new ConstraintSet(goal,
		null), SetAsListOfMetavariable.EMPTY_SET, services);
    }
    
    @Override
    public Name name() {
	return new Name(this.displayName());
    }
    
    @Override
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[2];

	toReturn[0] = "simplify";
	toReturn[1] = filename;

	return toReturn;
    }
    
    protected SmtSolver.RESULTTYPE answerType(String answer) {
	if (answer.indexOf("Valid") != -1) {
	    return SmtSolver.RESULTTYPE.VALID;
	} else if (answer.indexOf("Invalid") != -1) {
	    return SmtSolver.RESULTTYPE.INVALID;
	} else {
	    return SmtSolver.RESULTTYPE.UNKNOWN;
	}
    }
    
}
