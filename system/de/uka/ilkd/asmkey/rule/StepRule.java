// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.rule;


import de.uka.ilkd.asmkey.logic.AsmOperator;
import de.uka.ilkd.asmkey.logic.AsmUtil;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/** This class is a builtin rule to make a step from a world into the
 * (deterministic) subsequent world of the Kripke structure.
 *
 * @author Hubert Schmid
 */

public final class StepRule implements BuiltInRule {

    /** The builtin rule is applicable, if a top level formula with a
     * model box operator is selected. */
    public boolean isApplicable(Goal goal, PosInOccurrence pos, Constraint constraint) {
        if (pos == null || pos.posInTerm() != PosInTerm.TOP_LEVEL) {
            return false;
        } else {
            Term term = pos.constrainedFormula().formula();
            if (term.op() == AsmOperator.BOX) {
		if (pos.isInAntec()) {
		    return AsmUtil.isStatic(goal.sequent().succedent());
		} else {
		    return true;
		}
	    } else {
		return false;
	    } 
        }
    }

    /** This method creates a new goal. Let '[R] phi' be the selected
     * formula. Nothing happens to static formulas.  Formulas of the
     * form '[R] psi' are replaced by 'psi'. All other formulas are
     * removed.  */
    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
        Term term = ruleApp.posInOccurrence().constrainedFormula().formula();
        Debug.assertTrue(term.op() == AsmOperator.BOX);
        Term rule = term.sub(0);
        ListOfGoal result = goal.split(1);
        Goal newGoal = result.head();
        for (IteratorOfConstrainedFormula i = goal.sequent().antecedent().iterator(); i.hasNext();) {
            replace(newGoal, new PosInOccurrence(i.next(), PosInTerm.TOP_LEVEL, true), rule);
        }
        for (IteratorOfConstrainedFormula i = goal.sequent().succedent().iterator(); i.hasNext();) {
            replace(newGoal, new PosInOccurrence(i.next(), PosInTerm.TOP_LEVEL, false), rule);
        }
        return SLListOfGoal.EMPTY_LIST.append(newGoal);
    }

    /** This method does the actual replacement of {@link #apply}. */
    private static void replace(Goal goal, PosInOccurrence pio, Term rule) {
        ConstrainedFormula cf = pio.constrainedFormula();
        Term formula = cf.formula();
        if (AsmUtil.isStatic(formula)) {
            // nothing
        } else if (formula.op() == AsmOperator.BOX && formula.sub(0).equalsModRenaming(rule)) {
            // replace
            goal.changeFormula(new ConstrainedFormula(formula.sub(1), cf.constraint()), pio);
        } else {
            // remove
            goal.removeFormula(pio);
        }
    }
    
    public Name name() {
        return new Name("Step");
    }

    public String displayName() {
        return "Step";
    }

}
