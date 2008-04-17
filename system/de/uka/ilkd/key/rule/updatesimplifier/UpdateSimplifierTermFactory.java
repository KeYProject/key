// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.updatesimplifier;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.BoundVariableTools;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.util.Debug;

public class UpdateSimplifierTermFactory {
    

    /**
     * Interface for representing an ifEx cascade
     * <tt> ifEx (...) (phi1) (t1) (ifEx (...) (phi2) (t2) (...))</tt>. This
     * is essentially an iterator through the ifEx statements, starting with the
     * outermost one
     */
    public static interface IfExCascade {
        public Term getCondition ();
        
        public ArrayOfQuantifiableVariable getMinimizedVars ();
        
        // Information about the current ifEx statement. These methods must only
        // be called after having invoked <code>next</code> at least once
        
        public Term getThenBranch ();
        
        /**
         * @return <code>true</code> if a further ifEx statement is following
         *         (within the else-branch of the current statement)
         */
        public boolean hasNext ();
        
        /**
         * Step forward to the next ifEx statement
         */
        public void next ();
    }

    private final static TermFactory tf = TermFactory.DEFAULT;
    
    public final static UpdateSimplifierTermFactory DEFAULT = 
        new UpdateSimplifierTermFactory();
      
    private final Term unsatisfiableGuardCache = tf.createJunctorTerm ( Op.FALSE );

    private final Term validGuardCache = tf.createJunctorTerm ( Op.TRUE );
		
    
    public Term createIfExCascade (IfExCascade cascade, Term defaultTerm) {
        final List<IfExCascadeEntryBuilder> statements = 
            new LinkedList<IfExCascadeEntryBuilder> ();
        
        while ( cascade.hasNext () ) {
            cascade.next ();
            final IfExCascadeEntryBuilder builder =
                new IfExCascadeEntryBuilder ( cascade.getCondition (),
                                              cascade.getMinimizedVars (),
                                              cascade.getThenBranch () );
            if ( builder.isAlwaysElse () )
                // this statement can just be ignored and removed
                continue;

            statements.add ( 0, builder );

            if ( builder.isEndOfCascade () )
                // all further statements can be ignored
                break;
        }
        
        Term res = defaultTerm;
        
        final Iterator<IfExCascadeEntryBuilder> it = statements.iterator ();
        while ( it.hasNext () ) {
            final IfExCascadeEntryBuilder builder =
                it.next ();
            res = builder.createTerm ( res );
        }
        
        return res;
    }
    /**
     * creates an update term out of the given internal representation
     * used by the update simplifier, i.e. the assignmentpairs are made
     * explicit
     * @param target the term evaluated under the update
     * @return the update term <tt>{l1:=r1,...,ln:=rn}target</tt>
     */
    public Term createUpdateTerm(ArrayOfAssignmentPair assignmentPairs,
            Term target) {

        if (assignmentPairs.size() == 0) {
            return target;
        }

        final Term[] lhss = new Term[assignmentPairs.size()];
        final ArrayOfQuantifiableVariable[] boundVars = new ArrayOfQuantifiableVariable[assignmentPairs
                .size()];
        final Term[] guards = new Term[assignmentPairs.size()];
        final Term[] values = new Term[assignmentPairs.size()];

        for (int i = 0; i < assignmentPairs.size(); i++) {
            final AssignmentPair assignmentPair = assignmentPairs
                    .getAssignmentPair(i);
            boundVars[i] = assignmentPair.boundVars();
            guards   [i] = assignmentPair.guard();
            lhss     [i] = assignmentPair.locationAsTerm();
            values   [i] = assignmentPair.valueUnsafe();
            if (assignmentPair.location() == Update.StarLocation.ALL) {
                Debug.assertTrue(
                                i == assignmentPairs.size() - 1,
                                "Special star operator tried to escape. "
                                        + "(not allowed as long as no generalized terms)");
                return tf.createAnonymousUpdateTerm(
                        assignmentPair.value().op().name(), target);
            }
        }
        return tf.createQuanUpdateTerm(boundVars, guards, lhss, values, target);
    }

    /**
     * creates an update term out of the given internal representation
     * used by the update simplifier, i.e. the assignmentpairs are made
     * explicit
     * @param update an array of AssignmentPairs <tt>l:=r</tt> of the
     * simulataneous update to be created
     * @param target the term evaluated under the update
     * @return the update term <tt>{l1:=r1,...,ln:=rn}target</tt>
     */
    public Term createUpdateTerm(AssignmentPair[] update, Term target) 
    {
        return createUpdateTerm(new ArrayOfAssignmentPair(update), 
                target);
    }
    /**
     * @return the default termfactory for JavaCardDL terms
     */
    public TermFactory getBasicTermFactory() {    
        return tf;
    }
    
    
    public Term getUnsatisfiableGuard () {
        return unsatisfiableGuardCache;
    }
    
    public Term getValidGuard () {
        return validGuardCache;
    }
    
    /**
     * Compose the formula expressing that at least one of the conditions of an
     * ifEx-cascade evaluates to <tt>true</tt>, i.e. that the result of the
     * cascade is one of the then-branches (and not the default branch)
     */
    public Term matchingCondition (IfExCascade cascade) {
        Term res = getUnsatisfiableGuard ();
        
        while ( cascade.hasNext () ) {
            cascade.next ();
            final GuardSatisfiabilityFormulaBuilder builder =
                new GuardSatisfiabilityFormulaBuilder ( cascade.getCondition (),
                                                        cascade.getMinimizedVars () );
            res = getBasicTermFactory ()
                  .createJunctorTermAndSimplify ( Op.OR,
                                                  builder.createFormula (),
                                                  res );
        }
        
        return res;
    }
    
    private AssignmentPair renameBoundVars (AssignmentPair pair,
                                            ArrayOfQuantifiableVariable newVars) {
        final BoundVariableTools bvt = BoundVariableTools.DEFAULT;
        final ArrayOfQuantifiableVariable oldVars = pair.boundVars();
        
        return new AssignmentPairImpl
            ( newVars,
              bvt.renameVariables ( pair.guard (), oldVars, newVars ),
              pair.location (),
              bvt.renameVariables ( pair.locationSubs (), oldVars, newVars ),
              bvt.renameVariables ( pair.value (), oldVars, newVars ) );
    }

    
    private Term[] substitute(Term[] terms, ClashFreeSubst subst) {
        final Term[] newTerms = new Term[terms.length];
        boolean changed = false;
        for ( int i = 0; i != terms.length; ++i ) {
            newTerms[i] = subst.apply ( terms[i] );
            changed = changed || newTerms[i] != terms[i];
        }
        if ( changed ) return newTerms;
        return terms;
    }
    
    
    /**
     * Substitute <code>substTerm</code> for the variable <code>var</code> in
     * the given assignment pair. Ensures that no collisions occur.
     */
    public AssignmentPair substitute (AssignmentPair pair,
                                      QuantifiableVariable var,
                                      Term substTerm) {
        if ( !pair.freeVars ().contains ( var ) ) return pair;        
        
        final ClashFreeSubst subst = new ClashFreeSubst ( var, substTerm );

        pair = resolveCollisions ( pair, substTerm.freeVars () );
        
        return new AssignmentPairImpl ( pair.boundVars (),
                                        subst.apply ( pair.guard () ),
                                        pair.location (),
                                        substitute ( pair.locationSubs (),
                                                     subst ),
                                        subst.apply ( pair.value () ) );
    }

    
    /**
     * Substitute <code>substTerm</code> for the variable <code>var</code> in
     * the given update. Ensures that no collisions occur.
     */
    public Update substitute (Update update,
                              QuantifiableVariable var,
                              Term substTerm) {
        if ( !update.freeVars ().contains ( var ) ) return update;        
        
        final ArrayOfAssignmentPair pairs = update.getAllAssignmentPairs ();
        AssignmentPair newPairs[] = new AssignmentPair[pairs.size ()];

        for (int i = 0; i != pairs.size(); ++i)
            newPairs[i] = substitute ( pairs.getAssignmentPair ( i ),
                                       var,
                                       substTerm );

        return Update.createUpdate ( newPairs );
    }

    
    /**
     * Ensure that none of the variables <code>criticalVars</code> is bound by
     * <code>pair</code> (turns up in <code>pair.boundVars()</code>). When
     * necessary, variables are renamed to this end
     */
    public AssignmentPair resolveCollisions (AssignmentPair pair,
                                             SetOfQuantifiableVariable criticalVars) {
        final ArrayOfQuantifiableVariable oldVars = pair.boundVars();
        if ( oldVars.size() == 0 ) return pair;

        final BoundVariableTools bvt = BoundVariableTools.DEFAULT;

        final QuantifiableVariable newVars[] =
            new QuantifiableVariable [oldVars.size ()];
        if ( !bvt.resolveCollisions ( oldVars, newVars, criticalVars ) )
            return pair;
        
        return renameBoundVars ( pair, new ArrayOfQuantifiableVariable ( newVars ) );
    }
    
    /**
     * Ensure that none of the variables <code>criticalVars</code> is bound by
     * <code>update</code>. When necessary, variables are renamed to this end
     */
    public Update resolveCollisions (Update update,
                                     SetOfQuantifiableVariable criticalVars) {
        final ArrayOfAssignmentPair pairs = update.getAllAssignmentPairs ();
        AssignmentPair newPairs[] = new AssignmentPair[pairs.size ()];

        boolean changed = false;
        for (int i = 0; i != pairs.size(); ++i) {
            newPairs[i] = resolveCollisions ( pairs.getAssignmentPair ( i ),
                                              criticalVars );
            changed = changed || newPairs[i] != pairs.getAssignmentPair ( i );
        }
        
        if ( !changed ) return update;
        return Update.createUpdate ( newPairs );
    }
}
