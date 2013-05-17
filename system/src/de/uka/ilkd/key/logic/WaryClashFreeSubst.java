// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.*;

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
    private ImmutableSet<QuantifiableVariable> warysvars            = null;

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
	    newVarTerm = TB.var ( newVar );
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
	    if ( t.op () instanceof UpdateApplication )
		return applyOnUpdate   ( t );
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

	// only the last child is below the update
	final Term target = UpdateApplication.getTarget ( t );
	if ( !target.freeVars ().contains ( getVariable () ) )
	    return super.apply1 ( t );

	final Term[] newSubterms = new Term[t.arity()];
	@SuppressWarnings("unchecked")
    final ImmutableArray<QuantifiableVariable>[] newBoundVars =
	    new ImmutableArray[t.arity()];

	for ( int i = 0; i < t.arity (); i++ ) {
            if ( i != UpdateApplication.targetPos () )
                applyOnSubterm ( t, i, newSubterms, newBoundVars );
        }

	newBoundVars[UpdateApplication.targetPos()] = t.varsBoundHere ( UpdateApplication.targetPos() );
        final boolean addSubst =
            subTermChanges ( t.varsBoundHere ( UpdateApplication.targetPos () ), target );
        newSubterms[UpdateApplication.targetPos ()] = addSubst ? substWithNewVar ( target )
                                                   : target;

        return TB.tf().createTerm ( t.op (),
                               	    newSubterms,
                               	    getSingleArray(newBoundVars),
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
        return TB.subst(WarySubstOp.SUBST,
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
}
