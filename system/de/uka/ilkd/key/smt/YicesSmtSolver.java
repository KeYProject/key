package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SetAsListOfMetavariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.decproc.ConstraintSet;
import de.uka.ilkd.key.rule.RuleApp;

public class YicesSmtSolver extends AbstractSmtProver {

    /**
     * This rule's name.
     */
    public String displayName() {
	return "Yices";
    }

    /**
     * This rule's name as Name object.
     */
    public Name name() {
	return new Name(this.displayName());
    }

    /**
     * Set the abstract translator, that should be used to
     * 
     * @return the translator, that should be used.
     */
    protected AbstractSmtTranslator getTranslator(Goal goal, Services services,
	    RuleApp ruleApp) {
	return new SmtLibTranslator(goal.sequent(), new ConstraintSet(goal,
		null), SetAsListOfMetavariable.EMPTY_SET, services);
    }

    /**
     * Get the command for executing an external proofer.
     * 
     * @param filename
     *                the location, where the file is stored.
     * @param formula
     *                the formula, that was created by the translator.
     * @return Array of Strings, that can be used for executing an external
     *         decider.
     */
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[4];

	toReturn[0] = "yices";
	toReturn[1] = "-tc";
	toReturn[2] = "-smt";
	toReturn[3] = filename;

	return toReturn;
    }

    /**
     * 
     * @param answer
     *                the String answered by the external programm
     * @return VALID, if the formula was proven valid, INVALID, if the
     *         formula was proven invalid, UNKNOWN, if the formula could not
     *         be proved
     */
    protected int answerType(String answer) {
	if (answer.equals("unsat\n")) {
	    return VALID;
	} else if (answer.equals("sat\n")) {
	    return INVALID;
	} else {
	    return UNKNOWN;
	}
    }
}
