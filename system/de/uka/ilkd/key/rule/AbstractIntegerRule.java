// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureResult;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory;

/**
 * Abstract base class for ICS and Simplify built-in rules.
 */
public abstract class AbstractIntegerRule implements BuiltInRule {

    private final Name name;
    protected final boolean showResults;
    protected final DecisionProcedureTranslationFactory dptf;
    

    public AbstractIntegerRule(Name p_name, 
			       DecisionProcedureTranslationFactory dptf) {      
        this(p_name, true, dptf);
    }

    public AbstractIntegerRule(Name p_name, 
			       boolean resultWindow, 
			       DecisionProcedureTranslationFactory dptf) {
        name = p_name;
        showResults = resultWindow;
        this.dptf = dptf;
    }

    /**
     * returns true iff a rule is applicable at the given
     * position. This does not necessary mean that a rule application
     * will change the goal (this decision is made due to performance
     * reasons)
     */
    public boolean isApplicable(Goal            goal,               
				PosInOccurrence pio,
				Constraint      userConstraint) {
        if (pio == null) {
            return true;
        }
        return false;
    }

    public ListOfGoal apply ( Goal goal, Services services, RuleApp ruleApp ) {
        final BuiltInRuleApp birApp = (BuiltInRuleApp) ruleApp;
        final Constraint userConstraint = birApp.userConstraint ();
        final AbstractDecisionProcedure dp = getDecisionProcedure(goal,
				userConstraint, services);
        final DecisionProcedureResult result = dp.run ();
        
        ListOfGoal goals = null;

        if (result.getResult ()) {
            goals = SLListOfGoal.EMPTY_LIST;
            if (result.getConstraint () != Constraint.BOTTOM) {
                goals = goal.split ( 1 );
                goals.head ().addClosureConstraint ( result.getConstraint () );
            }
        }
        
        return goals;
    }

    /** 
     * clones this abstract integer rule and sets its decision procedure translation
     * factory to the given one 
     * @param dptf the {@link DecisionProcedureTranslationFactory} to be used by the 
     * cloned object
     * @return the cloned integer rule
     */
    public abstract AbstractIntegerRule clone(DecisionProcedureTranslationFactory dptf);
    
    /**
     * Get the decision procedure invoked by this rule.
     * @param goal the goal on which the decision procedure should operate.
     * @param userConstraint the user constraint
     * @return the decision procedure
     */
    protected abstract AbstractDecisionProcedure getDecisionProcedure ( Goal goal,
									Constraint userConstraint, Services services);

    public Name name () {
        return name;
    }

    public String displayName () {
        return name ().toString ();
    }

    public String toString () {
        return name ().toString ();
    }


}
