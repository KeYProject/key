// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.BoundVariableTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetAsListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.rule.updatesimplifier.ArrayOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.rule.updatesimplifier.UpdateSimplifierTermFactory;

/**
 * abstract class that must be extended by rules designed to be used
 * by the update simplifier
 */
public abstract class AbstractUpdateRule implements IUpdateRule {

    private final OldUpdateSimplifier updateSimplifier;

    /**
     * creates an instance of this rule used by the given update
     * simplifier
     * @param updateSimplifier the UpdateSimplifier using this rule
     */
    public AbstractUpdateRule(OldUpdateSimplifier updateSimplifier) {
	this.updateSimplifier = updateSimplifier;
    }

    /**
     * returns the update simplifier for which this rule has been
     * registered
     */
    public OldUpdateSimplifier updateSimplifier() {
	return updateSimplifier;
    }

    /**
     *  returns true if casting term <code>newSub</code> is necessary if
     *  it should replace the <code>pos</code>-th position of <code>t</code>   
     */
    private boolean needsCast(Term t, Term newSub, int pos, Services services) {
        if (newSub.sort().extendsTrans(t.sub(pos).sort())) {
            return false;
        }
        final Sort maxSort = TermHelper.getMaxSort(t, pos, services);      
        return !newSub.sort().extendsTrans(maxSort);
    }
    
    
    /**
     * TODO: here we have to check for collisions!!! /PR
     * 
     * propagates the update to the subterm of the given term
     * @param update the Update to be propagated
     * @param term the Term whose subterms have to be simplified
     * @param services the Services object
     * @return the simplified subterm, an array of bound variables 
     *  and a flag indicating if one of the subterms has changed
     */
    protected PropagationResult propagateUpdateToSubterms(Update update, 
	    						  Term term, 
	    						  Services services) {
        final Term[] subs = new Term[term.arity()];
        final ArrayOfQuantifiableVariable[] vars = 
            new ArrayOfQuantifiableVariable[subs.length];
        
        boolean changed =
            BoundVariableTools.DEFAULT
            .resolveCollisions (term, update.freeVars (), vars, subs);
        
        for (int i = 0; i<subs.length; i++) {
            final Term oldSub = subs[i];
            subs[i] = updateSimplifier().simplify(update, oldSub, services);
	    if (subs[i] != oldSub) {
		changed = true;		
		if (needsCast(term, subs[i], i, services) &&
		    subs[i].sort() instanceof AbstractSort) {		                        
                    subs[i] = UpdateSimplifierTermFactory.
			DEFAULT.getBasicTermFactory().
			createCastTerm((AbstractSort)oldSub.sort(), subs[i]);
		}
	    }
        }

        return new PropagationResult(subs, vars, changed);
    }
    
    /**
     * determines whether this rule is applicable for the pair of
     * update and target (the term on which the update will be
     * applied) term
     * @param update the Update to be applied on the given term
     * @param target the Term on which the update is applied
     * @return true if the rule can be applied on the update, target
     * pair 
     */   
    public abstract boolean isApplicable(Update update, Term target);
    
    
    public static class PropagationResult {
        private final Term[] subs;
        private final boolean changeFlag;
        private final ArrayOfQuantifiableVariable[] vars;
        
        public PropagationResult(Term[] subs, 
				 ArrayOfQuantifiableVariable[] vars,
				 boolean changeFlag) {
            this.subs = subs;
            this.vars = vars;
            this.changeFlag = changeFlag;
        }

        /**
         * @return the simplified subterms
         */
        public Term[] getSimplifiedSubterms() {            
            return subs;
        }
        
        public ArrayOfQuantifiableVariable[] getBoundVariables() {
            return vars;
        }
        /**
         * @return if one of the sub terms has been changed, true is returned
         */
        public boolean hasChanged() {           
            return changeFlag;
        }
    }


    /**
     * @param result
     */
    protected void logExit(Term result) {        
	/*
	 System.out.println("result is " + result);
	*/
    }

    /**
     * @param update
     * @param target
     */
    protected void logEnter(Update update, Term target) {
	/*
	  System.out.println("Rule: " + this.getClass() );        
	  System.out.println("apply " + update + " on " + target);        
	*/
	
    }

    
    protected static abstract class IterateAssignmentPairsIfExCascade
                    implements UpdateSimplifierTermFactory.IfExCascade {

        private final UpdateSimplifierTermFactory utf =
            UpdateSimplifierTermFactory.DEFAULT;

        private int locNum;
        private final ArrayOfAssignmentPair pairs;
        private AssignmentPair currentPair;

        public IterateAssignmentPairsIfExCascade (ArrayOfAssignmentPair pairs) {
            this.pairs = pairs;
            this.locNum = pairs.size ();
        }

        public ArrayOfQuantifiableVariable getMinimizedVars () {
            return getCurrentPair ().boundVars ();
        }

        public Term getThenBranch () {
            return getCurrentPair ().value ();
        }

        public boolean hasNext () {
            return locNum > 0;
        }

        public void next () {
            --locNum;
            currentPair =
                utf.resolveCollisions ( pairs.getAssignmentPair ( locNum ),
                                        criticalVars () );
        }

        protected AssignmentPair getCurrentPair () {
            return currentPair;
        }

        /**
         * Variables that must not turn up as result of
         * <code>getMinimizedVars()</code>. This method has to be overridden
         * by subclasses to give a hint about which variables that are bound in
         * the treated update have to be renamed
         */
        protected abstract SetOfQuantifiableVariable criticalVars ();

        protected static SetOfQuantifiableVariable freeVars (ArrayOfTerm terms) {
            SetOfQuantifiableVariable res = SetAsListOfQuantifiableVariable.EMPTY_SET;
            for ( int i = 0; i != terms.size (); ++i )
                res = res.union ( terms.getTerm ( i ).freeVars () );
            return res;
        }
    }

}
