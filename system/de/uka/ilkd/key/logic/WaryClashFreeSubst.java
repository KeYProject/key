// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.soundness.SVSkolemFunction;

public class WaryClashFreeSubst extends ClashFreeSubst {

    /** depth of recursion of the <code>apply</code> method */
    private int                       depth            = 0;
    /** the formula should be prepended with a quantifier */
    private boolean                   createQuantifier = false;

    /** variable with which the original variable should be
     * substituted below modalities */
    private QuantifiableVariable      newVar           = null;
    private Term                      newVarTerm       = null;

    /** variables occurring within the original term and within the
     * term to be substituted */
    private SetOfQuantifiableVariable warysvars            = null;
   
    public WaryClashFreeSubst ( QuantifiableVariable v, Term s ) {
	super ( v, s );
	warysvars = null;
    }

    /** 
     * substitute <code>s</code> for <code>v</code> in <code>t</code>,
     * avoiding collisions by replacing bound variables in
     * <code>t</code> if necessary.
     */
    public Term apply(Term t) {
	Term res;

	if ( depth == 0 ) {
	    if ( !getSubstitutedTerm ().isRigid () )
		findUsedVariables ( t );
	}

	++depth;
	try {
	    res = super.apply ( t );
	} finally { --depth; }

	if ( createQuantifier && depth == 0 ) res = addWarySubst ( res );
    
	return res;
    }

    /**
     * Determine a set of variables that do already appear within
     * <code>t</code> or the substituted term, and whose names should
     * not be used for free variables
     */
    private void findUsedVariables ( Term t ) {
	VariableCollectVisitor vcv;

	vcv   = new VariableCollectVisitor ();
	getSubstitutedTerm ().execPostOrder ( vcv );
	warysvars = vcv.vars ();

	vcv   = new VariableCollectVisitor ();
	t.execPostOrder ( vcv );
	warysvars = warysvars.union ( vcv.vars () );	
    }

    /**
     * Create a new logic variable to be used for substitutions below
     * modalities
     */
    private void createVariable () {
	if ( !createQuantifier ) {
	    createQuantifier = true;
	    
	    if ( getSubstitutedTerm ().freeVars ().contains ( getVariable () ) )
                // in this case one might otherwise get collisions, as the
                // substitution might be carried out partially within the scope
                // of the original substitution operator
	        newVar = newVarFor ( getVariable (), warysvars );
	    else
	        newVar = getVariable ();
	    newVarTerm = tf.createVariableTerm ( (LogicVariable)newVar );
	}	
    }

    /**
     * substitute <code>s</code> for <code>v</code> in
     * <code>t</code>, avoiding collisions by replacing bound
     * variables in <code>t</code> if necessary.  It is
     * assumed, that <code>t</code> contains a free occurrence of
     * <code>v</code>.
     */
    protected Term apply1(Term t) {
	// don't move to a different modality level
	if ( !getSubstitutedTerm ().isRigid () ) {
	    if ( t.op () instanceof Modality )
		return applyOnModality ( t );		
	    if ( t.op () instanceof IUpdateOperator )
		return applyOnUpdate   ( t );
	    if ( t.op () instanceof SVSkolemFunction )
		return applyToSVSkolem ( t );
	}
	return super.apply1 ( t );
    }

    /**
     * Apply the substitution (that replaces a variable with a
     * non-rigid term) on t, which has a modality as top-level
     * operator. This is done by creating a (top-level) existential
     * quantifier. This method is only called from <code>apply1</code>
     * for substitutions with non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private Term applyOnModality ( Term t ) {
	return applyBelowModality ( t );
    }

    /**
     * Apply the substitution (that replaces a variable with a
     * non-rigid term) on t, which has an update operator as top-level
     * operator. This is done by creating a (top-level) existential
     * quantifier. This method is only called from <code>apply1</code>
     * for substitutions with non-rigid terms
     *
     * PRECONDITION: <code>warysvars != null</code>
     */
    private Term applyOnUpdate ( Term t ) {
        final IUpdateOperator updOp = (IUpdateOperator)t.op ();
        
	// only the last child is below the update
	final Term target = updOp.target ( t );
	if ( !target.freeVars ().contains ( getVariable () ) )
	    return super.apply1 ( t );

	final Term[] newSubterms = new Term[t.arity()];
	final ArrayOfQuantifiableVariable[] newBoundVars =
	    new ArrayOfQuantifiableVariable[t.arity()];

	for ( int i = 0; i < t.arity (); i++ ) {
            if ( i != updOp.targetPos () )
                applyOnSubterm ( t, i, newSubterms, newBoundVars );
        }

	newBoundVars[updOp.targetPos()] = t.varsBoundHere ( updOp.targetPos() );
        final boolean addSubst =
            subTermChanges ( t.varsBoundHere ( updOp.targetPos () ), target );
        newSubterms[updOp.targetPos ()] = addSubst ? substWithNewVar ( target )
                                                   : target;

        return tf.createTerm ( t.op (),
                               newSubterms,
                               newBoundVars,
                               t.javaBlock ());
    }

    /**
     * Apply the substitution to a term/formula below a modality or update
     */
    private Term applyBelowModality (Term t) {
        return substWithNewVar ( t );
    }

    /**
     * Prepend the given term with a wary substitution (substituting
     * <code>newVar</code> with <code>getSubstitutedTerm()</code>)
     */
    private Term addWarySubst (Term t) {
        createVariable ();
        return tf.createSubstitutionTerm ( Op.SUBST,
                                           newVar,
                                           getSubstitutedTerm (),
                                           t );
    }

    /**
     * Rename the original variable to be substituted to <code>newVar</code> 
     */
    private Term substWithNewVar (Term t) {
        createVariable ();
        final ClashFreeSubst cfs = new ClashFreeSubst ( getVariable (),
                                                        newVarTerm );
        return cfs.apply ( t );
    }
    
    /**
     * Apply the substitution to a non-rigid skolem function
     */
    private Term applyToSVSkolem ( Term t ) {
    	return applyBelowModality(t);
    }

}
