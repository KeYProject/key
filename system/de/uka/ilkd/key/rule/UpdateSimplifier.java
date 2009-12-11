// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.updatesimplifier.*;
import de.uka.ilkd.key.util.Debug;


/**
 *  The update simplifier applies updates on tems/formulas. Therefore 
 * it can be initialiazed with a set of simplification rules that 
 * shall be used.
 * 
 * Calling the simplifier from outside must only be done by using 
 * the apply methods. The simplify methods are only for recursive 
 * calls made by the update simplification rules.   
 */
public class UpdateSimplifier {
    

    /**
     * List of rules used for simplifying update terms. The first
     * applicable rule is taken. 
     */
    private IUpdateRule[] simplificationRules = new IUpdateRule[0];

    /**
     * if set to true, the update simplifier is a bit more eagerly when
     * applying updates
     */
    private boolean eager = true;
    
    
    private Constraint formulaConstraint = Constraint.BOTTOM;

    public UpdateSimplifier() {       
        this(false, false);
    }
    
    /**
     * creates an instance of the update simplifier 
     * @param deletionEnabled a boolean flag indicating if unused or 
     * effectless assignment pairs should be removed
     * @param eager boolean true if updates shall be applied eagerly
     */
    public UpdateSimplifier(boolean deletionEnabled, boolean eager) {
	this.eager = eager;
        ImmutableList<IUpdateRule> usRules = ImmutableSLList.<IUpdateRule>nil().    
        append(new ApplyOnAnonymousUpdate(this)).
        append(new ApplyAnonymousUpdateOnNonRigid(this)).
        append(new ApplyOnUpdate(this)).
        append(new ApplyOnLocalVariableOrStaticField(this)).
        append(new ApplyOnAttributeAccess(this)).
        append(new ApplyOnArrayAccess(this)).
        append(new ApplyOnModality(this, deletionEnabled)).
        append(new ApplyOnRigidTerm(this)).
        append(new ApplyOnRigidOperatorTerm(this)).
        append(new ApplyOnHeapDependentLocation(this, deletionEnabled)).
        append(new ApplyOnProgramMethod(this, deletionEnabled)).
        append(new ApplyOnNonRigidWithExplicitDependencies(this)).
        append(new ApplyOnNonRigidTerm(this));
        
        this.setSimplificationRules(usRules);        
    }

    /**
     * Uses the given rules for update simplification. The order is
     * important as the first applicable rule is taken.
     * @param rules a IList<UpdateRule> to use for update
     * simplification
     */
    public void setSimplificationRules(ImmutableList<IUpdateRule> rules) {
	simplificationRules = rules.toArray(new IUpdateRule[rules.size()]);
    }

    
    public Term simplify(Update update, Term t, Services services) {
        for (IUpdateRule simplificationRule : simplificationRules) {
            if (simplificationRule.isApplicable(update, t)) {
                return simplificationRule.apply(update, t, services);
            }
        }
	return t;
    }

    /**
     * Derive a formula that describes in which cases the top-level operator
     * (location) described by <code>target</code> is updated by the given
     * update.
     * 
     * @param update
     *            the modification of function interpretations that is
     *            considered
     * @param target
     *            description of the location we are interested in;
     *            precondition: <code>target.op() instanceof Location</code>
     * @param services
     *            services object
     * @return formula that evaluates to <tt>true</tt> iff <code>update</code>
     *         evaluates to a semantic update that affects the location
     *         described by <code>target</code>
     */
    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        for (IUpdateRule simplificationRule : simplificationRules) {
            if (simplificationRule.isApplicable(update, target))
                return simplificationRule.matchingCondition(update, target, services);
        }
        Debug.fail("Don't know how to handle " + target);
        return null; // unreachable
    }
    
    /**
     * applies the update on the given term
     */
    public Term apply(Term t, Services services) {	
        formulaConstraint = Constraint.BOTTOM;
	// simplification and application part	
	return simplify(Update.createUpdate(t), t.sub(t.arity()-1), services);
    }


    /**
     * returns the formula constraint of the formula to be simpliefied
     * @return the formula constraint 
     */
    public Constraint formulaConstraint() {
        return formulaConstraint;
    }
    
    /**
     * 
     */
    public ConstrainedFormula apply(ConstrainedFormula target, 
				    Constraint userConstraint) {
	formulaConstraint = target.constraint();
        return target;
    }

    /**
     * @param target the Term with the update as top level operator whose application
     * is performed
     * @return the simplified term
     */
    public Term simplify(Term target, Services services) {
        if (target.op() instanceof IUpdateOperator) {            
	    target = simplify ( Update.createUpdate ( target ),
				( (IUpdateOperator)target.op () ).target ( target ),
				services);
	    if (!eager) {
		return target;
	    }
        }

        final Term[] subs = new Term[target.arity()];
        final ImmutableArray<QuantifiableVariable>[] vars = 
            new ImmutableArray[target.arity()];
        
        boolean changed = false;
        for (int i = 0; i<subs.length; i++) {
            subs[i] = simplify(target.sub(i), services);
            // only true as long as no bound variables change
            vars[i] = target.varsBoundHere(i);
            if (!changed && !(subs[i].equals(target.sub(i)))) {
                changed = true;
            }
        }
        return changed ? UpdateSimplifierTermFactory.DEFAULT.
                getBasicTermFactory().
                createTerm(target.op(), subs, vars, 
                        target.javaBlock()) : target ;
    }
}
