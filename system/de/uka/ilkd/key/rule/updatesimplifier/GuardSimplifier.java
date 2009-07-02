// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.WaryClashFreeSubst;
import de.uka.ilkd.key.logic.op.*;


/**
 *
 */
public abstract class GuardSimplifier {

    private Term condition;

    private ListOfQuantifiableVariable minimizedVars;

    public GuardSimplifier (Term condition,
                            ArrayOfQuantifiableVariable arMinimizedVars) {
        this.condition = condition;
        this.minimizedVars = toList ( arMinimizedVars );
    }

    public boolean bindsVariables () {
        return !getMinimizedVars().isEmpty ();
    }

    public boolean isValidGuard () {
        return getCondition().op () == Junctor.TRUE;
    }

    public boolean isUnsatisfiableGuard () {
        return getCondition().op () == Junctor.FALSE;            
    }
    
    /**
     * @return the formula that is simplified by <code>this</code>
     */
    public Term getCondition () {
        return condition;
    }

    /**
     * @return variables that are supposed to represent minimum individuals for
     *         which the guard is satisfied
     */
    protected ListOfQuantifiableVariable getMinimizedVars () {
        return minimizedVars;
    }

    private boolean isMinimizedVar (Operator op) {
        if ( !( op instanceof QuantifiableVariable ) ) return false;
        return getMinimizedVars().contains ( (QuantifiableVariable)op );
    }

    /**
     * Simplify the treated formula. This removes trivial equations (same left
     * and right term) and employs equations of the shape <tt> x = t </tt>
     * (where <tt>x</tt> is a minimized variable) to substitute the variable
     * with the term <tt>t</tt>. This method is supposed to be called in the
     * end of constructors of subclasses
     */
    protected void simplify () {
        while ( !getMinimizedVars().isEmpty () ) {
            final PairOfQuantifiableVariableAndTerm definingPair =
                findSimpleEquation ( getCondition() );
            if ( definingPair == null ) break;
            substituteTempl ( definingPair.variable, definingPair.term );
        }
        
        this.condition = elimSimpleStuff ( getCondition() );
        
        this.minimizedVars = neededVars ( getMinimizedVars() );
    }

    /**
     * Method that needs to be implemented by subclasses, this determines which
     * of the bound/minimized variables are actually needed. The method is
     * supposed to select certain elements of <code>allVars</code> without
     * changing their order
     */
    private ListOfQuantifiableVariable neededVars (ListOfQuantifiableVariable allVars) {
        ListOfQuantifiableVariable needed = SLListOfQuantifiableVariable.EMPTY_LIST;
        
        ListOfQuantifiableVariable innerVars = allVars;
        while ( !innerVars.isEmpty () ) {
            final QuantifiableVariable var = innerVars.head ();
            innerVars = innerVars.tail ();
            // order is important
            if ( !innerVars.contains ( var ) && isNeededVarTempl ( var ) )
                needed = needed.append ( var );
        }
        return needed;
    }

    /**
     * Template method for deciding whether <code>var</code> is a variable
     * that is necessary or that can be removed
     */
    private boolean isNeededVarTempl (final QuantifiableVariable var) {
        return getCondition ().freeVars ().contains ( var )
               || isNeededVar ( var );
    }

    /**
     * Supposed to be overridding in subclasses
     */
    protected boolean isNeededVar (QuantifiableVariable var) {
        return false;
    }

    /**
     * Used to implement <code>simplify()</code>, find trivial parts of the
     * guard and remove them
     */
    private Term elimSimpleStuff (Term formula) {
        final UpdateSimplifierTermFactory utf = UpdateSimplifierTermFactory.DEFAULT;
        final TermFactory tf = utf.getBasicTermFactory ();
        
        if ( formula.op () == Equality.EQUALS ) {
            if ( formula.sub ( 0 ).equalsModRenaming ( formula.sub ( 1 ) ) )
                return utf.getValidGuard ();
        } else if ( formula.op () instanceof Junctor ) {
            final Junctor junc = (Junctor)formula.op ();
            final Term[] subTerms = new Term [formula.arity ()];
            for ( int i = 0; i != subTerms.length; ++i )
                subTerms[i] = elimSimpleStuff ( formula.sub ( i ) );
            if ( subTerms.length == 2 )
                return tf.createJunctorTermAndSimplify ( junc,
                                                         subTerms[0],
                                                         subTerms[1] );
            return tf.createJunctorTerm ( junc, subTerms );
        }
    
        return formula;
    }

    /**
     * Template method to substitute <code>var</code> with
     * <code>substTerm</code> (called from <code>simplify()</code>)
     * wherever this is necessary. The hole <code>substitute()</code> can be
     * filled by subclasses
     */
    private void substituteTempl (QuantifiableVariable var, Term substTerm) {
        this.minimizedVars = getMinimizedVars().removeAll ( var );

        this.condition = subst ( var, substTerm, getCondition () );

        substitute ( var, substTerm );
    }

    protected Term subst (QuantifiableVariable var,
                          Term substTerm,
                          Term termToBeModified) {
        final WaryClashFreeSubst subst = new WaryClashFreeSubst ( var, substTerm );
        return subst.apply ( termToBeModified );
    }

    /**
     * Substitute <code>var</code> with <code>substTerm</code> (called from
     * <code>doSubstitute()</code>) wherever this is necessary. This can be
     * overridden by subclasses that need this information
     */
    protected void substitute (QuantifiableVariable var, Term substTerm) {}
    
    private ListOfQuantifiableVariable toList (ArrayOfQuantifiableVariable ar) {
        ListOfQuantifiableVariable res = SLListOfQuantifiableVariable.EMPTY_LIST;
        for ( int i = ar.size () - 1; i >= 0; --i )
            res = res.prepend ( ar.getQuantifiableVariable ( i ) );
        return res;
    }

    /**
     * Recursively search for equations <tt> x = t </tt> (or similar)
     * 
     * @return the pair <tt> (x, t) </tt> in case of success (for the first
     *         equation found), <code>null</code> otherwise
     */
    private PairOfQuantifiableVariableAndTerm findSimpleEquation (Term formula) {
        if ( formula.op () == Equality.EQUALS ) {
            final PairOfQuantifiableVariableAndTerm pair =
                isSimpleEquation ( formula, 0 );
            if ( pair != null ) return pair;
            
            return isSimpleEquation ( formula, 1 );
        } else if ( formula.op () == Junctor.AND ) {
            final PairOfQuantifiableVariableAndTerm pair =
                findSimpleEquation ( formula.sub ( 0 ) );
            if ( pair != null ) return pair;
            
            return findSimpleEquation ( formula.sub ( 1 ) );
        }
        
        return null;
    }

    private PairOfQuantifiableVariableAndTerm isSimpleEquation (Term formula,
                                                                int varLocation) {
        if ( !isMinimizedVar ( formula.sub ( varLocation ).op () ) )
            return null;
    
        final QuantifiableVariable var =
            (QuantifiableVariable)formula.sub ( varLocation ).op ();
        final Term value = formula.sub ( 1 - varLocation );
    
        if ( value.freeVars ().contains ( var )
             || !value.sort ().extendsTrans ( var.sort () ) ) return null;
    
        return new PairOfQuantifiableVariableAndTerm ( var, value );
    }

    private static class PairOfQuantifiableVariableAndTerm {
        public final QuantifiableVariable variable;
        public final Term term;
        
        public PairOfQuantifiableVariableAndTerm (QuantifiableVariable variable,
                                                  Term term) {
            this.variable = variable;
            this.term = term;
        }
    }

}
