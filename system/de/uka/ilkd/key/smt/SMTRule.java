package de.uka.ilkd.key.smt;

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

    private final SmtSolver prover;

    public SMTRule(SmtSolver arg1) {
	this.prover = arg1;
    }

    /**
     * This rule's name.
     */
    public String displayName() {
	return prover.name();
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
	if (pio == null) {
	    return true;
	} else {
	    return false;
	}
    }

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {

	SmtSolver.RESULTTYPE valid = this.prover.isValid(goal, ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getTimeout(), services);
	if (valid == SmtSolver.RESULTTYPE.VALID) {
	    return SLListOfGoal.EMPTY_LIST;
	} else {
	    return null;
	}
    }

}
