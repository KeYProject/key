package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

public class SMTRule implements BuiltInRule {

    private SmtSolver prover = null;

    public SMTRule(SmtSolver arg1) {
	this.prover = arg1;
    }

    /**
     * This rule's name.
     */
    public String displayName() {
	return prover.displayName();
    }

    /**
     * This rule's name as Name object.
     */
    public Name name() {
	return prover.name();
    }

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {

	//only make applicable, if the complete goal should be proved
	if (pio == null) {
	    return true;
	} else {
	    return false;
	}
	//return this.prover.isApplicable(goal);
    }

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {

	SmtSolver.RESULTTYPE valid = this.prover.isValid(goal, 60*60*1, services, ruleApp);
	if (valid == SmtSolver.RESULTTYPE.VALID) {
	    return SLListOfGoal.EMPTY_LIST;
	} else if (valid == SmtSolver.RESULTTYPE.UNKNOWN) {
	    return null;
	} else if (valid == SmtSolver.RESULTTYPE.INVALID) {
	    ListOfGoal toReturn = SLListOfGoal.EMPTY_LIST;
	    //TODO add new goal, that implies invalidity
	    return null;
	} else {
	    return null;
	}
    }

}
