// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.*;



/**
 * Factory providing the update constructors that are described in "Sequential,
 * Parallel and Quantified Updates of First-Order Structures". Don't try to use
 * this class together with anonymous updates, this would probably screw up
 * everything horribly.
 * 
 * TODO: so far, updates are not simplified during construction; the factory
 * could be optimized
 */
public class UpdateFactory {
    
    /**
     * Context of the updates that are produced by the factory.
     */
    private final Services services; 
    
    /**
     * the update simplifier to be used
     */
    private final UpdateSimplifier simplifier;
    
    private final TermFactory        tf            = TermFactory.DEFAULT;
    private final UpdateSimplifierTermFactory utf  =
                                            UpdateSimplifierTermFactory.DEFAULT;
   
    public UpdateFactory (Services services, UpdateSimplifier simplifier) {
        this.services = services;
        this.simplifier = simplifier;
    }

    private Term wellOrder (Term t1, Term t2) {
        // TODO: pretty hackish, better replace this with some real code /PR 
        
        final IntegerLDT integerLDT =
            services.getTypeConverter ().getIntegerLDT ();
        
        if ( t1.sort ().extendsTrans(integerLDT.targetSort ())
             && t2.sort ().extendsTrans(integerLDT.targetSort ()) ) {     // integer case
            final Function WORelation =
                (Function)services.getNamespaces ().functions ()
                               .lookup ( new Name ( "quanUpdateLeqInt" ) );
            assert WORelation != null :
                                "Update factory could not find   "
                                + "well-ordering for integers";
            
            return tf.createFunctionTerm ( WORelation, t1, t2 );
        }
        
        //TEST
        System.out.println("UF: Sorts are " + t1.sort() + "("  + t1.sort().hashCode() + ") and " + t2.sort() + "(" + t2.sort().hashCode() + ")");
        System.out.println("correct int sort is: " + integerLDT.targetSort() + "(" + integerLDT.targetSort().hashCode() + ")");
        System.exit(-1);

        assert false : "Update factory can currently not handle the"
                     + " sorts of the terms " + t1 + ", " + t2;
        return null; // unreachable
    }
    
    /**
     * Apply an update to a term or a formula, without simplifying the result
     */
    public Term prepend(Update update, Term target) {
        return UpdateSimplifierTermFactory.DEFAULT
               .createUpdateTerm ( services, update.getAllAssignmentPairs (), target );
    }
    
    /**
     * Apply an update to a term or a formula, simplify the result
     */
    public Term apply(Update update, Term target) {
        return getSimplifier ().simplify ( update, target, services );
    }
    
    
    /**
     * Apply an update to another update
     */
    public Update apply(Update update, Update target) {
        final ArrayOfAssignmentPair oldPairs = target.getAllAssignmentPairs ();

        final AssignmentPair[] newPairs = new AssignmentPair[oldPairs.size ()];
        boolean changed = false;
        for ( int i = 0; i != oldPairs.size (); ++i ) {
            newPairs[i] = apply ( update, oldPairs.getAssignmentPair ( i ) );
            changed = changed || newPairs[i] != oldPairs.getAssignmentPair ( i );
        }

        if ( !changed ) return target;
        
        return Update.createUpdate ( newPairs );
    }    
    
    
    /**
     * Apply an update to an assignment pair
     */
    private AssignmentPair apply (Update update, AssignmentPair oriTarget) {
        final AssignmentPair cleanedTarget =
            utf.resolveCollisions ( oriTarget, update.freeVars () );

        boolean changed = false;
        
        final Term[] locSubs = new Term [cleanedTarget.locationSubs().length];
        for (int i = 0; i != locSubs.length; ++i) {
            locSubs[i] = apply ( update, cleanedTarget.locationSubs ()[i] );
            changed = changed || locSubs[i] != cleanedTarget.locationSubs ()[i];
        }

        /** unsafe is safe in this case, as the evaluated value will be used on the 
         * right side of an update
         */
        final Term newValue = apply ( update, cleanedTarget.valueUnsafe() );
        changed = changed || newValue != cleanedTarget.valueUnsafe();
        
        final Term newGuard = apply (update, cleanedTarget.guard());
        changed = changed || newGuard != cleanedTarget.guard ();
        
        if ( !changed ) return oriTarget;
        return new AssignmentPairImpl ( cleanedTarget.boundVars (),
                                        newGuard,
                                        cleanedTarget.location (),
                                        locSubs,
                                        newValue );
    }
    
    
    /**
     * The neutral update (neutral element concerning parallel and sequential
     * composition) not updating anything
     */
    public Update skip () {
        return Update.createUpdate ( new AssignmentPair [0] );
    }

    /**
     * Create an elementary update <tt>leftHandSide := value</code>
     * 
     * @param leftHandSide
     *            Term describing the location that is updated. The operator of
     *            the term has to implement the interface <code>Location</code>.
     * @param value
     *            Term describing the new value of the updated location
     * 
     * @return the resulting update
     */    
    public Update elementaryUpdate (Term leftHandSide, Term value) {
        final Term[] subs = new Term [leftHandSide.arity ()];
        for ( int i = 0; i != subs.length; ++i )
            subs[i] = leftHandSide.sub ( i );
        
        final AssignmentPair ass =
            new AssignmentPairImpl ( (Location)leftHandSide.op (), subs, value );
        
        return Update.createUpdate ( new AssignmentPair [] { ass } );
    }
    
    /**
     * Compute the parallel composition of two updates,
     * <tt>update1 | update2</tt>
     */
    public Update parallel (Update update1, Update update2) {
        final ArrayOfAssignmentPair pairs1 = update1.getAllAssignmentPairs();
        final ArrayOfAssignmentPair pairs2 = update2.getAllAssignmentPairs();
        
        final AssignmentPair[] resPairs =
            new AssignmentPair [pairs1.size() + pairs2.size()];
        
        pairs1.arraycopy ( 0, resPairs, 0, pairs1.size () );
        pairs2.arraycopy ( 0, resPairs, pairs1.size (), pairs2.size () );
        
        return Update.createUpdate ( resPairs );
    }

    /**
     * Compute the parallel composition of an array of updates.
     * 
     * TODO: this could be implemented more efficiently
     */
    public Update parallel (Update[] updates) {
        if ( updates.length == 0 ) return skip ();

        Update res = updates[0];
        for ( int i = 1; i != updates.length; ++i )
            res = parallel ( res, updates[i] );

        return res;
    }
    
    /**
     * Compute the sequential composition of two updates,
     * <tt>update1 ; update2</tt>
     */
    public Update sequential (Update update1, Update update2) {
        return parallel ( update1, apply ( update1, update2 ) );
    }
    
    /**
     * Compute the sequential composition of an array of updates.
     */
    public Update sequential (Update[] updates) {
        if ( updates.length == 0 ) return skip ();

        Update res = updates[0];
        for ( int i = 1; i != updates.length; ++i )
            res = sequential ( res, updates[i] );

        return res;
    }
    
    
    public Update quantify (QuantifiableVariable[] vars, Update update) {
        Update res = update;
        for (int i = 0; i < vars.length; i++) {
            res = quantify (vars[i], res);
        }
        return res;
    }
    
    
    /**
     * Quantify over <code>var</code>, i.e. carry out the update
     * <code>update</code> in parallel for all values of <code>var</code>
     */
    public Update quantify (QuantifiableVariable var, Update update) {
        // ensure that no collisions occur later on
        update = utf.resolveCollisions ( update, update.freeVars () );
        
        final ArrayOfAssignmentPair oldPairs = update.getAllAssignmentPairs ();
        
        // we create a copy of the update in which <tt>var</tt> is replaced with
        // a new variable <tt>var'</tt>
        final LogicVariable varP = createPrime ( var );
        final ArrayOfAssignmentPair oldPairsP =
            substitute ( update, var, varP ).getAllAssignmentPairs();
        
        // sanity check
        assert oldPairs.size () == oldPairsP.size ();
        
        return quantify ( var, varP, oldPairs, oldPairsP );
    }
    
    /**
     * Perform quantification over <code>var</code> for the update described
     * by <code>oldPairs</code>. Therefore it is necessary to add certain
     * guards to the elementary updates, and a copy <code>oldPairsP</code> of
     * the update is needed in which <code>var</code> is renamed to
     * <code>varP</code>
     * 
     * @param var
     *            variable to quantify over
     * @param varP
     *            new variable necessary to render the guards
     * @param oldPairs
     *            update that is supposed to be quantified
     * @param oldPairsP
     *            update that differs from <code>oldPairs</code> in the
     *            renaming of <code>var</code> to <code>varP</code>
     * @return resulting (simplified) update
     */
    private Update quantify (QuantifiableVariable var,
                             LogicVariable varP,
                             ArrayOfAssignmentPair oldPairs,
                             ArrayOfAssignmentPair oldPairsP) {
        final AssignmentPair[] newPairs = new AssignmentPair [oldPairs.size ()];
        for ( int locNum = 0; locNum != oldPairs.size (); ++locNum ) {
            final AssignmentPair pair = oldPairs.getAssignmentPair ( locNum );
            
            final Term newGuard;
            if ( pair.locationAsTerm().freeVars ().contains ( var ) ) {
                final Term clashCond = clashConditions ( var,
                                                         varP,
                                                         pair,
                                                         firstNPairs ( oldPairsP,
                                                                       locNum ) );
                newGuard = tf.createJunctorTermAndSimplify ( Junctor.AND,
                                                             clashCond,
                                                             pair.guard () );                
            } else {
                newGuard = pair.guard ();
            }
            
            newPairs[locNum] = new AssignmentPairImpl ( pushFront ( var, pair ),
                                                        newGuard,
                                                        pair.location (),
                                                        pair.locationSubs (),
                                                        pair.value () );
        }
        return Update.createUpdate ( newPairs );
    }

    /**
     * Add <code>var</code> as first bound variable of <code>pair</code>
     */
    private ArrayOfQuantifiableVariable pushFront (QuantifiableVariable var,
                                                   AssignmentPair pair) {
        final int oldSize = pair.boundVars ().size ();
        final QuantifiableVariable[] newBoundVars =
            new QuantifiableVariable [oldSize + 1];
        newBoundVars[0] = var;
        pair.boundVars ().arraycopy ( 0, newBoundVars, 1, oldSize );

        return new ArrayOfQuantifiableVariable ( newBoundVars );
    }

    /**
     * Conditions under which the elementary update <code>pair</code> may be
     * executed, i.e. conditions under which its application does not collide
     * with the earlier part <code>prefix</code> of the whole update. It is
     * necessary to impose these conditions because distributing quantification
     * through the parallel composition operator changes the order of update
     * execution
     */
    private Term clashConditions (QuantifiableVariable var,
                                  LogicVariable varP,
                                  AssignmentPair pair,
                                  Update prefix) {
        Term res = getSimplifier().matchingCondition ( prefix, pair.locationAsTerm (), services );
        if ( res.op () == Junctor.FALSE )
            return UpdateSimplifierTermFactory.DEFAULT.getValidGuard ();

// Bug in the first implementation: It is wrong to add quanifiers here        
//        if ( pair.boundVars ().size () > 0 )
//            res = tf.createQuantifierTerm ( Op.EX, pair.boundVars (), res );
        res = tf.createJunctorTerm ( Junctor.NOT, res );
        
        final Term var2varPComparison =
            wellOrder ( tf.createVariableTerm ( (LogicVariable)var ),
                        tf.createVariableTerm ( varP ) );

        res = tf.createJunctorTermAndSimplify ( Junctor.OR, var2varPComparison, res );
        return tf.createQuantifierTerm ( Op.ALL, varP, res );
    }

    private Update firstNPairs (ArrayOfAssignmentPair pairs, int n) {
        final AssignmentPair[] criticalPairs = new AssignmentPair [n];
        pairs.arraycopy ( 0, criticalPairs, 0, n );
        return Update.createUpdate ( criticalPairs );
    }

    private LogicVariable createPrime (QuantifiableVariable var) {
        // TODO: name the new variable in a better way
        return new LogicVariable ( new Name ( var.name ().toString () + "Prime" ),
                                   var.sort () );
    }

    private Update substitute (Update update,
                               QuantifiableVariable var,
                               LogicVariable varPrime) {
        return utf.substitute ( update, var, tf.createVariableTerm ( varPrime ) );
    }

    /**
     * Add the guard <code>guard</code> as a condition to <code>update</code>,
     * i.e. only carry out the update if <code>guard</code> evaluates to true
     */
    public Update guard (Term guard, Update update) {
        assert guard.sort () == Sort.FORMULA;
        
        final Update cleanedUpdate =
            utf.resolveCollisions ( update, guard.freeVars () );
        final ArrayOfAssignmentPair oldPairs =
            cleanedUpdate.getAllAssignmentPairs ();
        
        final AssignmentPair[] newPairs =
            new AssignmentPair [cleanedUpdate.locationCount ()];
        for ( int i = 0; i != oldPairs.size (); ++i ) {
            final AssignmentPair pair = oldPairs.getAssignmentPair ( i );
            final Term newGuard =
                tf.createJunctorTermAndSimplify ( Junctor.AND, guard, pair.guard () );
            newPairs[i] = new AssignmentPairImpl ( pair.boundVars (),
                                                   newGuard,
                                                   pair.location (),
                                                   pair.locationSubs (),
                                                   pair.value () );
        }
        return Update.createUpdate ( newPairs );
    }
    
    private UpdateSimplifier getSimplifier () {
        return simplifier;
    }
}
