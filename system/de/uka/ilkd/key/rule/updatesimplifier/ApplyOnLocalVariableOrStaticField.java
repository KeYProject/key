// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SetAsListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.OldUpdateSimplifier;

/**
 * Rule used by the update simplifier as application of an update on
 * a local variable or static variable
 * Implements rule (S1) described in ....
 */
public class ApplyOnLocalVariableOrStaticField extends AbstractUpdateRule {

    /**
     * creates an instance of this rule used by the given update
     * simplifier
     */
    public ApplyOnLocalVariableOrStaticField(OldUpdateSimplifier us) {
	super(us);
    }

    /**
     * determines whether this rule is applicable for the pair of
     * update and target (the term on which the update will be
     * applied) term. 
     * @param update the Update to be applied on target
     * @param target the Term on which the update is applied
     * @return true if the top level operator of target is a local
     * variable
     */
    public boolean isApplicable(Update update, Term target) {	
	return target.op() instanceof LocationVariable;
    }

    /**     
     */
    public Term apply(Update update, Term target, Services services) {
        logEnter(update, target);
	
        final Term result =
            UpdateSimplifierTermFactory.DEFAULT
            .createIfExCascade ( createCascade ( update, target ), target );
        
	logExit(result);

	return result;
    }
    
    private PVIfExCascade createCascade (Update update, Term target) {
        return new PVIfExCascade ( update.getAssignmentPairs
                                   ( (UpdateableOperator)target.op () ) );
    }

    private static class PVIfExCascade extends IterateAssignmentPairsIfExCascade {
        
        public PVIfExCascade (ArrayOfAssignmentPair pairs) {
            super ( pairs );
        }
        
        public Term getCondition () {
            return getCurrentPair ().guard ();
        }
        
        protected SetOfQuantifiableVariable criticalVars () {
            return SetAsListOfQuantifiableVariable.EMPTY_SET;
        }
    }
    
    public Term matchingCondition (Update update, Term target, Services services) {
        return UpdateSimplifierTermFactory.DEFAULT
            .matchingCondition ( createCascade ( update, target ) );
    }
}
