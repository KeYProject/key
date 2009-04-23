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

import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.util.Debug;

/**
 * This class describes a position in an occurrence of a term. A
 * ConstrainedFormula and a PosInTerm determine an object of this 
 * class exactly. 
 */
public class PosInOccurrence {

    public static PosInOccurrence findInSequent(Sequent seq, 
                                                int formulaNumber, 
                                                PosInTerm pos) {
       return new PosInOccurrence(seq.getFormulabyNr(formulaNumber),  
                                  pos, seq.numberInAntec(formulaNumber));
    }
    
    /**
     * the constrained formula the pos in occurrence describes
     */
    private final ConstrainedFormula cfma;

    // saves 8 bytes (due to allignment issues) per instance if we use a 
    // short here instead of an int
    private final short hashCode;
    
    /**
     * is true iff the position is in the antecedent of a sequent. 
     */
    private final boolean inAntec;   
    

    private final PosInTerm metaPosInTerm;

    // Descend into metavariables instantiations
    private final Term      metaTerm;

    /** the position in cfma.formula() */
    private final PosInTerm posInTerm;

    /**
     * The subterm this object points to, or <code>null</code>
     */
    private Term subTermCache=null;

    public PosInOccurrence(ConstrainedFormula cfma, 
			   PosInTerm posInTerm, 
			   boolean inAntec) {
        this(cfma, posInTerm, null, null, inAntec);
    }

    private PosInOccurrence(ConstrainedFormula cfma, 
            PosInTerm posInTerm,
            Term metaTerm, PosInTerm metaPosInTerm,
            boolean inAntec) {	
	this.inAntec=inAntec;
	this.cfma=cfma;	
	this.posInTerm=posInTerm;
	this.metaTerm=metaTerm;
	this.metaPosInTerm=metaPosInTerm;
	this.hashCode = (short) computeHash ();
    }
       
    
    private int computeHash () {
        int res = constrainedFormula().hashCode() * 13 + posInTerm().hashCode();
	if ( termBelowMetavariable() != null )
    	    res += termBelowMetavariable().hashCode() * 13 +
    	        posInTermBelowMetavariable().hashCode();
    	return res;
    }
    
    
    /**
     * returns the ConstrainedFormula that determines the occurrence of
     * this PosInOccurrence 
     */
    public ConstrainedFormula constrainedFormula() {
	return cfma;
    }

    /**
     * @return Depth of the represented position within a formula; top-level
     *         positions (<code>isTopLevel()</code> have depth zero
     */
    public int depth () {
        int res = posInTerm ().depth ();

        if ( termBelowMetavariable () != null )
            res += posInTermBelowMetavariable ().depth ();

        return res;
    }

    /**
     * creates a new PosInOccurrence that has exactly the same state as this
     * object except the PosInTerm is new and walked down the specified
     * subterm, as specified in method down of 
     * {@link de.uka.ilkd.key.logic.PosInTerm}.
     */
    public PosInOccurrence down(int i) {
        if ( metaTerm == null )
	    return new PosInOccurrence(cfma, posInTerm.down(i), inAntec);
	else
	    return new PosInOccurrence(cfma, posInTerm, metaTerm, metaPosInTerm.down(i),
				       inAntec);
    }
    
    /** 
     * compares this PosInOccurrence with another PosInOccurrence
     * and returns true if both describe the same occurrence 
     */
    public boolean eqEquals(Object obj) {
	if (!(obj instanceof PosInOccurrence)) {
	    return false;
	}
	final PosInOccurrence cmp = (PosInOccurrence)obj;

	if ( !constrainedFormula ().equals ( cmp.constrainedFormula () ) ) {
	    return false;
        }
    
	return equalsHelp ( cmp );
    } 

    /**
     * Contrary to <code>eqEquals</code>, this method returns true only for pio
     * objects that point to the same (identical) formula
     * @param obj
     * @return true if both objects are equal
     */
    public boolean equals (Object obj) {
	if (!(obj instanceof PosInOccurrence)) {
	    return false;
	}
	final PosInOccurrence cmp = (PosInOccurrence)obj;

	// NB: the class <code>NonDuplicateAppFeature</code> depends on the usage
	// of <code>!=</code> in this condition
	if ( constrainedFormula() != cmp.constrainedFormula() ) {
	    return false;
	}
    
	return equalsHelp ( cmp );
    }

    private boolean equalsHelp (final PosInOccurrence cmp) {
        if ( isInAntec () == cmp.isInAntec () ) {
            if ( !posInTerm ().equals ( cmp.posInTerm () ) ) return false;

            if ( termBelowMetavariable () == null )
                return cmp.termBelowMetavariable () == null;
            else
                return termBelowMetavariable ()
                               .equals ( cmp.termBelowMetavariable () )
                       && posInTermBelowMetavariable ()
                               .equals ( cmp.posInTermBelowMetavariable () );
        }
        return false;
    }

    /**
     * @return the number/index of the deepest subterm that this
     *         <code>PosInOccurrence</code> points to. If the position is
     *         top-level, the result will be <code>-1</code>
     */
    public int getIndex() {
        if ( metaTerm == null || metaPosInTerm == PosInTerm.TOP_LEVEL )
                return posInTerm.getIndex ();
        return metaPosInTerm.getIndex ();
    }

    public int hashCode () {
    	return (int) hashCode;
    }  

    /**
     * returns true iff the occurrence is in the
     * antecedent of a sequent. 
     */
    public boolean isInAntec() {	
	return inAntec;
    }

    public boolean isTopLevel () {
	return
	    posInTerm == PosInTerm.TOP_LEVEL &&
	    ( metaTerm == null || metaPosInTerm == PosInTerm.TOP_LEVEL );
    }

    /**
     * List all subterms between the root and the position this
     * objects points to; the first term is the whole term
     * <code>constrainedFormula().formula()</code>, the last one
     * <code>subTerm()</code>
     * @return an iterator that walks from the root of the term to the
     * position this <code>PosInOccurrence</code>-object points to
     */
    public PIOPathIterator iterator () {
	return new PIOPathIteratorImpl ();
    }

    /**
     * The usage of this method is strongly discouraged, use 
     * {@link PosInOccurrence#iterator} instead.     
     * describes the exact occurence of the refered term inside 
     * {@link ConstrainedFormula#formula()} 
     * @returns the position in the formula of the ConstrainedFormula of
     * this PosInOccurrence. 
     */
    public PosInTerm posInTerm() {
	return posInTerm;
    }

    /**
     *  The usage of this method is strongly discouraged, use 
     * {@link PosInOccurrence#iterator} instead.    
     */
    public PosInTerm posInTermBelowMetavariable () {
	return metaPosInTerm;
    }     

    /**
     * Replace the formula this object points to with the new formula given
     * 
     * @param p_newFormula
     *                the new formula
     * @return a <code>PosInOccurrence</code> object that points to the same
     *         position within the formula <code>p_newFormula</code> as this
     *         object does within the formula <code>constrainedFormula()</code>.
     *         It is not tested whether this position exists within <code>p_newFormula</code>
     */
    public PosInOccurrence replaceConstrainedFormula (ConstrainedFormula p_newFormula) {
        final PIOPathIterator it = iterator ();
        Term newTerm = p_newFormula.formula ();
        PosInTerm newPosInTerm = PosInTerm.TOP_LEVEL;
        int depth = 0;

        while ( true ) {
            final int subNr = it.next ();


            if ( newTerm.op () instanceof Metavariable && depth == posInTerm ().depth() ) {
                // It is necessary to insert a term below the metavariable,
                // as the iterator still holds further elements

                return new PosInOccurrence ( p_newFormula,
                                             posInTerm (),
                                             termBelowMetavariable (),
                                             posInTermBelowMetavariable (),                                          
                                             inAntec );
            }

            if ( subNr == -1 ) break;

            newPosInTerm = newPosInTerm.down( subNr );
            newTerm = newTerm.sub ( subNr );
            ++depth;
        }

        return new PosInOccurrence ( p_newFormula,
                                     newPosInTerm,
                                     inAntec);
    }

        
    /**
     * If "this" points to a metavariable, a term can be inserted at
     * this position, allowing to walk down the term further "inside"
     * the metavariable.
     */
    public PosInOccurrence setTermBelowMetavariable ( Term p_metaTerm ) {
	if (Debug.ENABLE_ASSERTION) {
            Debug.assertTrue ( metaTerm == null &&
                    ( constrainedFormula().formula().subAt(posInTerm).op()
                            instanceof Metavariable ) &&
			   p_metaTerm.sort().extendsTrans
			   ( constrainedFormula().formula().subAt(posInTerm).sort() ),
			   "Illegal position (no metavariable) or incompatible sorts" );
        }

	return new PosInOccurrence(cfma, posInTerm, p_metaTerm, PosInTerm.TOP_LEVEL,
	        inAntec);
    }
    

    /**
     * returns the subterm this object points to
     */
    public Term subTerm () {
	if ( subTermCache == null ) {
	    if ( metaTerm == null )
		subTermCache = constrainedFormula().formula().subAt(posInTerm);
	    else
		subTermCache = metaTerm.subAt ( metaPosInTerm );
	}
	return subTermCache;
    }


    /** The usage of this method is strongly discouraged, use 
     * {@link PosInOccurrence#iterator} instead if possible.
     */     
    public Term termBelowMetavariable () {
	return metaTerm;
    }


    /**
     * Ascend to the top node of the formula this object points to 
     */
    public PosInOccurrence topLevel () {
        if (isTopLevel()) {
            return this;
        }
	return new PosInOccurrence(cfma, PosInTerm.TOP_LEVEL, 
				   inAntec);    	
    }


    /** toString */
    public String toString() {
	String res = "Term "+
	    posInTerm()+" of "+ constrainedFormula();
	if ( termBelowMetavariable() != null )
	    res +=  " / Term "+
		posInTermBelowMetavariable()+" of "+ termBelowMetavariable();
	return res;
//            formulaNumberInSequent()+" th formula";

    }



    /**
     * Ascend to the parent node
     */
    public PosInOccurrence up() {
	assert !isTopLevel() : "not possible to go up from top level position";
	if ( metaTerm == null || metaPosInTerm == PosInTerm.TOP_LEVEL )
	    return new PosInOccurrence(cfma, posInTerm.up(), 
				       inAntec);
	else
	    return new PosInOccurrence(cfma, posInTerm, metaTerm, metaPosInTerm.up(),
				       inAntec);	    
    }

    
    private class PIOPathIteratorImpl implements PIOPathIterator {
	boolean           belowMetavariable = false;
	int               child;
	int               count             = 0;
	IntIterator       currentPathIt;
	Term              currentSubTerm    = null;
	
	private PIOPathIteratorImpl               () {
	    currentPathIt = posInTerm ().iterator ();
	}

	private PosInTerm firstN ( PosInTerm p_pit,
				   int       p_n ) {
	    IntIterator it  = p_pit.iterator ();
	    PosInTerm         res = PosInTerm.TOP_LEVEL;

	    while ( p_n-- != 0 )
		res = res.down ( it.next () );

	    return res;
	}

	/**
	 * @return the number of the next child on the path, or
	 * <code>-1</code> if no further child exists (this is the number
	 * that was also returned by the last call of <code>next()</code>)
	 */
	public int             getChild           () {
	    return child;
	}

	/**
	 * @return the current position within the term
	 * (i.e. corresponding to the latest <code>next()</code>-call)
	 */
	public PosInOccurrence getPosInOccurrence () {
	    // the object is created only now to make the method
	    // <code>next()</code> faster

	    final PosInOccurrence pio;
	    if ( belowMetavariable ) {
	        pio = new PosInOccurrence ( cfma,
                                            posInTerm,
                                            metaTerm,
                                            firstN ( metaPosInTerm,
                                                     count - posInTerm.depth () - 1 ),
                                            inAntec );
	    } else {
	        pio = new PosInOccurrence ( cfma,
                                            firstN ( posInTerm, count - 1 ),
                                            inAntec );            
	    }
        
	    return pio;
	}

	/**
	 * @return the current subterm this object points to
	 * (i.e. corresponding to the latest <code>next()</code>-call);
	 * this method satisfies
	 * <code>getPosInOccurrence().subTerm()==getSubTerm()</code>
	 */
	public Term            getSubTerm         () {
	    return currentSubTerm;
	}

	public boolean         hasNext            () {
	    return currentPathIt != null;
	}

	/**
	 * @return the number of the next child on the path, or
	 * <code>-1</code> if no further child exists
	 */
	public int         next               () {
	    int res;

	    if ( currentSubTerm == null )
		currentSubTerm = cfma.formula ();
	    else
		currentSubTerm = currentSubTerm.sub ( child );

	    if ( currentPathIt.hasNext () )
		res = currentPathIt.next ();
	    else if ( !belowMetavariable &&
		      termBelowMetavariable () != null ) {
		belowMetavariable = true;
		currentPathIt     = posInTermBelowMetavariable ().iterator ();
		currentSubTerm    = termBelowMetavariable ();

		if ( currentPathIt.hasNext () )
		    res = currentPathIt.next ();
		else {
		    res           =  -1 ;
		    currentPathIt = null;
		}
	    } else {
		res           =  -1 ;
		currentPathIt = null;
	    }

	    child = res;
	    ++count;
	    return res;
	}
    }
	
}
