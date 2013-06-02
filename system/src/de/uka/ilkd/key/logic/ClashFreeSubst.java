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
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

public class ClashFreeSubst {
    protected static final TermBuilder TB = TermBuilder.DF;

    QuantifiableVariable v;
    Term s;
    ImmutableSet<QuantifiableVariable> svars;

    public ClashFreeSubst(QuantifiableVariable v,Term s) {
	this.v = v;
	this.s = s;
	svars = s.freeVars();
    }

    protected QuantifiableVariable getVariable () {
	return v;
    }

    protected Term getSubstitutedTerm () {
	return s;
    }

    /** substitute <code>s</code> for <code>v</code> in <code>t</code>,
     * avoiding collisions by replacing bound variables in
     * <code>t</code> if necessary.
     */
    public Term apply(Term t) {
	if ( ! t.freeVars().contains(v) ) {
	    return t;
	} else
	    return apply1 ( t );
    }

    /** substitute <code>s</code> for <code>v</code> in
     * <code>t</code>, avoiding collisions by replacing bound
     * variables in <code>t</code> if necessary.  It is
     * assumed, that <code>t</code> contains a free occurrence of
     * <code>v</code>. */
    protected Term apply1(Term t) {
	if ( t.op() == v ) {
	    return s;
	} else {
	    return applyOnSubterms(t);
	}
    }

    //XXX
    protected static ImmutableArray<QuantifiableVariable> getSingleArray(ImmutableArray<QuantifiableVariable>[] bv) {
	if(bv == null) {
	    return null;
	}
	ImmutableArray<QuantifiableVariable> result = null;
	for(ImmutableArray<QuantifiableVariable> arr : bv) {
	    if(arr != null && !arr.isEmpty()) {
		if(result == null) {
		    result = arr;
		} else {
		    assert arr.equals(result) : "expected: " + result + "\nfound: " + arr;
		}
	    }
	}
	return result;
    }

    /** substitute <code>s</code> for <code>v</code> in
     * every subterm of <code>t</code>, and build a new term.
     * It is assumed, that one of the subterms contains a free occurrence
     * of <code>v</code>, and that the case <code>v==t<code> is already
     * handled. */
    private Term applyOnSubterms(Term t) {
	final int arity = t.arity();
	final Term[] newSubterms = new Term[arity];
	@SuppressWarnings("unchecked")
    final ImmutableArray<QuantifiableVariable>[] newBoundVars =
	    new ImmutableArray[arity];
	for ( int i=0; i<arity; i++ ) {
	    applyOnSubterm ( t, i, newSubterms, newBoundVars );
        }
	return TB.tf().createTerm(t.op(), newSubterms, getSingleArray(newBoundVars), t.javaBlock());
    }

    /**
     * Apply the substitution of the subterm <code>subtermIndex</code> of
     * term/formula <code>completeTerm</code>. The result is stored in
     * <code>newSubterms</code> and <code>newBoundVars</code> (at index
     * <code>subtermIndex</code>)
     */
    protected void applyOnSubterm (Term completeTerm,
                                   int subtermIndex,
                                   Term[] newSubterms,
                                   ImmutableArray<QuantifiableVariable>[] newBoundVars) {
        if ( subTermChanges ( completeTerm.varsBoundHere ( subtermIndex ),
                              completeTerm.sub ( subtermIndex ) ) ) {
            final QuantifiableVariable[] nbv =
                new QuantifiableVariable [completeTerm.varsBoundHere ( subtermIndex ).size ()];
            applyOnSubterm ( 0,
                             completeTerm.varsBoundHere ( subtermIndex ),
                             nbv,
                             subtermIndex,
                             completeTerm.sub ( subtermIndex ),
                             newSubterms );
            newBoundVars[subtermIndex] = new ImmutableArray<QuantifiableVariable> ( nbv );
        } else {
            newBoundVars[subtermIndex] = completeTerm.varsBoundHere ( subtermIndex );
            newSubterms[subtermIndex] = completeTerm.sub ( subtermIndex );
        }
    }

    /** Perform the substitution on <code>subTerm</code> bound by the
     * variables in <code>boundVars</code>, starting with the variable
     * at index <code>varInd</code>.  Put the resulting bound
     * variables (which might be new) into <code>newBoundVars</code>,
     * starting from position <code>varInd</code>, and the resulting
     * subTerm into <code>newSubterms[subInd]</code>.
     * <P> It is assumed that <code>v</code> occurrs free in
     * in this quantified subterm, i.e. it occurrs free in
     * <code>subTerm</code>, but does not occurr in
     * <code>boundVars</code> from <code>varInd</code> upwards..
     */
    private void applyOnSubterm(int varInd,
				ImmutableArray<QuantifiableVariable> boundVars,
				QuantifiableVariable[] newBoundVars,
				int subInd,
				Term subTerm,
				Term[] newSubterms
				) {
	if ( varInd >= boundVars.size() ) {
	    newSubterms[subInd] = apply1(subTerm);
	} else {
	    QuantifiableVariable qv = boundVars.get(varInd);
	    if ( svars.contains(qv) ) {
		/* Here is the clash case all this is about! Hurrah! */

		// Determine Variable names to avoid
		VariableCollectVisitor vcv = new VariableCollectVisitor();
		ImmutableSet<QuantifiableVariable> usedVars;
		subTerm.execPostOrder(vcv);
		usedVars = svars;
		usedVars = usedVars.union(vcv.vars());
		for ( int i = varInd+1; i < boundVars.size(); i++ ) {
		    usedVars =
			usedVars.add(boundVars.get(i));
		}
		// Get a new variable with a fitting name.
		QuantifiableVariable qv1 = newVarFor(qv,usedVars);

		// Substitute that for the old one.
		newBoundVars[varInd] = qv1;
		new ClashFreeSubst(qv, TB.var(qv1))
		    .applyOnSubterm1(varInd+1, boundVars, newBoundVars,
				    subInd,subTerm,newSubterms);
		// then continue recursively, on the result.
		applyOnSubterm(varInd+1,
			       new ImmutableArray<QuantifiableVariable>(newBoundVars),
			       newBoundVars,
			       subInd,newSubterms[subInd],newSubterms);
	    } else {
		newBoundVars[varInd] = qv;
		applyOnSubterm(varInd+1, boundVars, newBoundVars,
			       subInd, subTerm, newSubterms);
	    }
	}
    }

    /** Same as applyOnSubterm, but v doesn't have to occurr free in the
     * considered quantified subterm. It is however assumed that no more
     * clash can occurr. */
    private void applyOnSubterm1(int varInd,
				 ImmutableArray<QuantifiableVariable> boundVars,
				 QuantifiableVariable[] newBoundVars,
				 int subInd,
				 Term subTerm,
				 Term[] newSubterms
				 ) {
	if ( varInd >= boundVars.size() ) {
	    newSubterms[subInd] = apply(subTerm);
	} else {
	    QuantifiableVariable qv = boundVars.get(varInd);
	    newBoundVars[varInd] = qv;
	    if ( qv == v ) {
		newSubterms[subInd] = subTerm;
		for( int i = varInd; i<boundVars.size(); i++) {
		    newBoundVars[i] = boundVars.get(varInd);
		}
	    } else {
		applyOnSubterm1(varInd+1, boundVars, newBoundVars,
				subInd, subTerm, newSubterms);
	    }
	}
    }

    /** returns true if <code>subTerm</code> bound by
     * <code>boundVars</code> would change under application of this
     * substitution.  This is the case, if <code>v</code> occurrs free
     * in <code>subTerm</code>, but does not occurr in <code>boundVars</code>.
     * @returns true if <code>subTerm</code> bound by
     * <code>boundVars</code> would change under application of this
     * substitution
     */
    protected boolean subTermChanges(ImmutableArray<QuantifiableVariable> boundVars,
                                     Term subTerm) {
	if ( !subTerm.freeVars().contains(v) ) {
	    return false;
	} else {
	    for( int i = 0; i<boundVars.size(); i++ ) {
		if ( v == boundVars.get(i) ) {
		    return false;
		}
	    }
	}
	return true;
    }

    /** returns a new variable that has a name derived from that of
     * <code>var</code>, that is different from any of the names of
     * variables in <code>usedVars</code>.
     * <P> Assumes that <code>var</code> is a @link{LogicVariable}. */
    protected QuantifiableVariable newVarFor(QuantifiableVariable var,
					     ImmutableSet<QuantifiableVariable> usedVars) {
	LogicVariable lv = (LogicVariable) var;
	String stem = var.name().toString();
	int i = 1;
	while ( ! nameNewInSet( (stem + i), usedVars ) ) {
	    i++;
	}
	return new LogicVariable( new Name(stem+i), lv.sort() );
    }

    /** returns true if there is no object named <code>n</code> in the
     * set <code>s</code> */
    private boolean nameNewInSet(String n, ImmutableSet<QuantifiableVariable> qvars) {
        for (QuantifiableVariable qvar : qvars) {
            if (qvar.name().toString().equals(n)) {
                return false;
            }
        }
	return true;
    }

    // This helper is used in other places as well. Perhaps make it toplevel one
    // day.
    /** A Visitor class to collect all (not just the free) variables
     * occurring in a term. */
    public static class VariableCollectVisitor extends DefaultVisitor {
	/** the collected variables */
	private ImmutableSet<QuantifiableVariable> vars;

	/** creates the Variable collector */
	public VariableCollectVisitor() {
	    vars = DefaultImmutableSet.<QuantifiableVariable>nil();
	}

	public void visit(Term t) {
	    if (t.op() instanceof QuantifiableVariable) {
		vars=vars.add((QuantifiableVariable)t.op());
	    } else {
		for ( int i = 0; i<t.arity(); i++ ) {
		    ImmutableArray<QuantifiableVariable> vbh = t.varsBoundHere(i);
		    for ( int j = 0; j<vbh.size(); j++ ) {
			vars = vars.add(vbh.get(j));
		    }
		}
	    }
	}

        /** the set of all occurring variables.*/
	public ImmutableSet<QuantifiableVariable> vars() {
	    return vars;
	}
    }

}
