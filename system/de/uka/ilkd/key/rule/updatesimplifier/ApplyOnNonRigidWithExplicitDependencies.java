// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.updatesimplifier;

import java.util.Arrays;
import java.util.HashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/**
 * This rule implements the update rule to be used for application on non rigid
 * functions with explicit dependency knowledge. The rule first sequentialzes
 * the simultaneous update and then propagates the independant part of the
 * update to the subterms. This rule may introduce <em>new</em> program
 * variables.
 */
public class ApplyOnNonRigidWithExplicitDependencies extends AbstractUpdateRule {

    /**
     * During update decomposition certain subterms <code>t</code>
     * are replaced by a new introduced variable <code>var</code>. 
     * This inner class helps in particular to keep track
     * of the pair <tt>(var, t)</tt> from which later new {@link AssignmentPair}s
     * are created.
     */
    public class ReplacementResult {

        private ListOfAssignmentPair assignmentPairs = 
            SLListOfAssignmentPair.EMPTY_LIST;
        private Term result;      
        
        /**
         * creates a new instance 
         */
        public ReplacementResult() {
            super();           
        }

        /**
         * @return true if changed
         */
        public boolean hasChanged() {            
            return !assignmentPairs.isEmpty();
        }

        /**
         * returns a new {@link AssignmentPair} 
         * @return list of assignmentPairs
         */
        public ListOfAssignmentPair getAssignmentPairs() {           
            return assignmentPairs;
        }

        /**
         * @return the resulting term
         */
        public Term getTerm() {            
            return result;
        }

        /**
         * @param replacementVar
         * @param term 
         */
        public void addAssignmentPair(LocationVariable replacementVar, Term term) {
            assignmentPairs = assignmentPairs.append(
                    new AssignmentPairImpl(replacementVar, new Term[0], 
                    term));               
        }

        /**
         * @param term
         */
        public void setReplacementResultTerm(Term term) {
            this.result = term;            
        }

    }
    private static final TermFactory BASIC_TERM_FACTORY = UpdateSimplifierTermFactory.DEFAULT
            .getBasicTermFactory();

    /**
     * Creates an instance of this rule for the given update simplifier
     * 
     * @param updateSimplifier
     *            the UpdateSimplifier where the rule will be used
     */
    public ApplyOnNonRigidWithExplicitDependencies(
            UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);
    }

    /**
     * This rule is applicable if the top operator of the target term is of kind
     * {@link de.uka.ilkd.key.logic.op.NRFunctionWithExplicitDependencies}
     * 
     * @param update
     *            the Update to be applied on the target term
     * @param target
     *            the Term on which the update is applied
     * @return true iff this rule is responsible for simplication of the given
     *         pair
     */
    public boolean isApplicable(Update update, Term target) {
        return target.op() instanceof NRFunctionWithExplicitDependencies;
    }

    /**
     * applies the update on the given target and returns the result. It is
     * assumed that
     * {@link ApplyOnNonRigidWithExplicitDependencies#isApplicable(Update, Term)}
     * has been called before and returned <tt>true</tt>
     * 
     * @param update
     *            the Update to be applied on <code>target</code>
     * @param target
     *            the Term with a top operator of kind
     *            {@link NRFunctionWithExplicitDependencies}on which the update
     *            is applied
     * @param services
     *            the Services object
     * @return the application result
     */
    public Term apply(Update update, Term target, Services services) {
        logEnter(update,target);
        final Update[] updates = sequentializeUpdate(update,
                (NRFunctionWithExplicitDependencies) target.op());
        Term result;
        if (updates[1] != null) {
            final PropagationResult pr = propagateUpdateToSubterms(updates[1], 
        	    						   target, 
        	    						   services);        
            result = pr.hasChanged() ? BASIC_TERM_FACTORY.createTerm(
                            target.op(), pr.getSimplifiedSubterms(),
                            pr.getBoundVariables(), target.javaBlock()) : 
                                target;
        } else {
            result = target;
        }

        result = (updates[0] != null ? UpdateSimplifierTermFactory.DEFAULT.createUpdateTerm(
                updates[0].getAllAssignmentPairs(), result) : result);                
        logExit(result);
        return result;
    }

    /**
     * @param update
     */
    private Update[] sequentializeUpdate(Update update,
            NRFunctionWithExplicitDependencies nr) {
        
        final ArrayOfAssignmentPair pairs = update.getAllAssignmentPairs();

        final Location[] nrLocs = new Location[nr.dependencies().size()];
        nr.dependencies().arraycopy(0, nrLocs, 0, nrLocs.length);

        HashSet<Location> nrDependencies = new HashSet<Location>();
        nrDependencies.addAll(Arrays.asList(nrLocs));

        ListOfAssignmentPair leftUpdate = SLListOfAssignmentPair.EMPTY_LIST;
        ListOfAssignmentPair rightUpdate = SLListOfAssignmentPair.EMPTY_LIST;
        // collect all assignment pairs with a location occuring in the
        // dependency list
        // as top operator on the left hand side
       for (int i = 0; i < pairs.size(); i++) {
            final AssignmentPair pair = pairs.getAssignmentPair(i);            
            Location pairLoc = pair.location();
            if (pairLoc instanceof AttributeOp) {
                pairLoc = (Location) ((AttributeOp)pairLoc).attribute();
            }
            if (nrDependencies.contains(pairLoc) ||
                    pair.nontrivialGuard() || pair.boundVars().size()>0 ||
                    nrDependencies.contains(pair.value().op())) {
                leftUpdate = leftUpdate.append(pair);
            } else {
                final Term[] locs = pair.locationSubs();
                Term value = pair.value();
                for (int j = 0, sz = locs.length; j<sz; j++) {
                    ReplacementResult res = replace(locs[j], nrDependencies);
                    if (res.hasChanged()) {
                        locs[j] = res.getTerm();
                        leftUpdate.append(res.getAssignmentPairs());
                    }
                }                
                ReplacementResult res = replace(value, nrDependencies);
                if (res.hasChanged()) {
                    value = res.getTerm();
                    leftUpdate.append(res.getAssignmentPairs());
                }
                rightUpdate = rightUpdate.append
                (new AssignmentPairImpl(pair.location(), locs, value));

            }
        }
        
        final Update[] updates = new Update[]{
                leftUpdate.isEmpty() ? null :  
                        Update.createUpdate(leftUpdate.toArray()),
                rightUpdate.isEmpty() ? null :
                    Update.createUpdate(rightUpdate.toArray())
        };        
        
        return updates;
    }

    private ReplacementResult replace(Term t, HashSet<Location> deps) {
        ReplacementResult result = new ReplacementResult();
        
        result.setReplacementResultTerm(replaceOccurences(t, deps, result));
        
        return result;
    }
    
    /**
     * it is assumed that t contains no variable binding terms TODO: full
     * support of quantified variables
     */
    private Term replaceOccurences(Term t, HashSet<Location> deps, 
            ReplacementResult res) {
        if (t.op() instanceof IUpdateOperator || deps.contains(t.op())) {
            return getReplacement(t, res);
        } else {
            Term result = t;
            final Term[] newSubs = new Term[t.arity()];
            final ArrayOfQuantifiableVariable[] quantifiedVars = 
                new ArrayOfQuantifiableVariable[t.arity()];
            boolean changed = false;
            for (int i = 0; i < t.arity(); i++) {
                newSubs[i] = replaceOccurences(t.sub(i), deps, res);
                if (newSubs[i] != t.sub(i)) {
                    changed = true;
                }
                quantifiedVars[i] = t.varsBoundHere(i);
            }
            return changed ? BASIC_TERM_FACTORY.createTerm(t.op(), newSubs,
                    quantifiedVars, t.javaBlock()) : result;
        }
    }

    private static long COUNTER = 0;

    private Term getReplacement(Term s, ReplacementResult res) {
        // TODO register new variables at namespace; use variablenameproposer;
        // get KeYJavaType 
        final LocationVariable replacementVar =
            new LocationVariable(new ProgramElementName("#pv"+COUNTER++), s.sort());       
        res.addAssignmentPair(replacementVar, s);
        return BASIC_TERM_FACTORY.createVariableTerm(replacementVar);
    }

    /**
     * as currently a {@link NRFunctionWithExplicitDependencies}is not a
     * location and can therefore not appear on the left hand side of an update
     * this method must not be called. If this changes in future (e.g. the
     * attribute operator becomes a subclass of this kind of operator) the
     * method has to be implemented.
     */
    public Term matchingCondition(Update update, 
	    			  Term target, 
	    			  Services services) {
        Debug.fail("matchingCondition(...) must not be called for target "
                + target);
        return null;
    }

}
