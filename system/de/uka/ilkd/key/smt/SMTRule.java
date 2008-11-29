package de.uka.ilkd.key.smt;

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

    private AbstractSmtProver prover = null;

    public SMTRule(AbstractSmtProver arg1) {
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

	return this.prover.isApplicable(goal);
    }

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {

	int valid = this.prover.isValid(goal, 30, services, ruleApp);
	if (valid == AbstractSmtProver.VALID) {
	    return SLListOfGoal.EMPTY_LIST;
	} else if (valid == AbstractSmtProver.UNKNOWN) {
	    return null;
	} else if (valid == AbstractSmtProver.INVALID) {
	    ListOfGoal toReturn = SLListOfGoal.EMPTY_LIST;
	    //TODO add new goal, that implies invalidity
	    return null;
	} else {
	    return null;
	}
    }

}
