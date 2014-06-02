// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

/**
 * This class describes a position in an occurrence of a term. A
 * SequentFormula and a PosInTerm determine an object of this 
 * class exactly. 
 */
public final class PosInOccurrence {

    public static PosInOccurrence findInSequent(Sequent seq, 
                                                int formulaNumber, 
                                                PosInTerm pos) {
       return new PosInOccurrence(seq.getFormulabyNr(formulaNumber),  
                                  pos, seq.numberInAntec(formulaNumber));
    }
    
    /**
     * the constrained formula the pos in occurrence describes
     */
    private final SequentFormula cfma;

    // saves 8 bytes (due to alignment issues) per instance if we use a
    // short here instead of an int
    private final short hashCode;
    
    /**
     * is true iff the position is in the antecedent of a sequent. 
     */
    private final boolean inAntec;

    /** the position in cfma.formula() */
    private final PosInTerm posInTerm;

    /**
     * The subterm this object points to, or <code>null</code>
     */
    private Term subTermCache = null;

    public PosInOccurrence(SequentFormula cfma,
                           PosInTerm posInTerm,
                           boolean inAntec) {
        assert posInTerm != null;
	this.inAntec=inAntec;
	this.cfma=cfma;	
	this.posInTerm=posInTerm;	
	this.hashCode = (short) computeHash ();
    }
       
    
    private int computeHash () {
        if (constrainedFormula() != null && posInTerm() != null) {
            return constrainedFormula().hashCode() * 13 + posInTerm().hashCode();
        } else if (constrainedFormula() != null) {
            return constrainedFormula().hashCode() * 13;
        } else if (posInTerm() != null) {
            return posInTerm().hashCode();
        } else {
            return 0;
        }
    }
    
    
    /**
     * returns the SequentFormula that determines the occurrence of
     * this PosInOccurrence 
     */
    public SequentFormula constrainedFormula() {
	return cfma;
    }

    /**
     * @return Depth of the represented position within a formula; top-level
     *         positions (<code>isTopLevel()</code> have depth zero
     */
    public int depth () {
        return posInTerm ().depth ();
    }

    /**
     * creates a new PosInOccurrence that has exactly the same state as this
     * object except the PosInTerm is new and walked down the specified
     * subterm, as specified in method down of 
     * {@link de.uka.ilkd.key.logic.PosInTerm}.
     */
    public PosInOccurrence down(int i) {
	return new PosInOccurrence(cfma, posInTerm.down(i), inAntec);
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
	    return posInTerm ().equals ( cmp.posInTerm () );
	}
        return false;
    }

    /**
     * @return the number/index of the deepest subterm that this
     *         <code>PosInOccurrence</code> points to. If the position is
     *         top-level, the result will be <code>-1</code>
     */
    public int getIndex() {
       return posInTerm.getIndex ();
    }

    public int hashCode () {
    	return hashCode;
    }  

    /**
     * returns true iff the occurrence is in the
     * antecedent of a sequent. 
     */
    public boolean isInAntec() {	
	return inAntec;
    }

    public boolean isTopLevel () {
	return posInTerm == PosInTerm.getTopLevel();
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
     * describes the exact occurrence of the referred term inside
     * {@link SequentFormula#formula()} 
     * @returns the position in the formula of the SequentFormula of
     * this PosInOccurrence. 
     */
    public PosInTerm posInTerm() {
	return posInTerm;
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
    public PosInOccurrence replaceConstrainedFormula (SequentFormula p_newFormula) {
        assert p_newFormula != null;
        final PIOPathIterator it = iterator ();
        Term newTerm = p_newFormula.formula ();
        PosInTerm newPosInTerm = PosInTerm.getTopLevel();

        while ( true ) {
            final int subNr = it.next ();
            
            if ( subNr == -1 ) break;

            newPosInTerm = newPosInTerm.down( subNr );
            newTerm = newTerm.sub ( subNr );
        }

        return new PosInOccurrence ( p_newFormula,
                                     newPosInTerm,
                                     inAntec);
    }

       
    

    /**
     * returns the subterm this object points to
     */
    public Term subTerm () {
	if ( subTermCache == null ) {
	    subTermCache = constrainedFormula().formula().subAt(posInTerm);
	}
	return subTermCache;
    }

    /**
     * Ascend to the top node of the formula this object points to 
     */
    public PosInOccurrence topLevel () {
        if (isTopLevel()) {
            return this;
        }
	return new PosInOccurrence(cfma, PosInTerm.getTopLevel(), 
				   inAntec);    	
    }


    /** toString */
    public String toString() {
	String res = "Term "+
	    posInTerm()+" of "+ constrainedFormula();
	
	return res;

    }



    /**
     * Ascend to the parent node
     */
    public PosInOccurrence up() {
	assert !isTopLevel() : "not possible to go up from top level position";

	return new PosInOccurrence(cfma, posInTerm.up(), 
		inAntec);

    }

    
    private class PIOPathIteratorImpl implements PIOPathIterator {	
	int               child;
	int               count             = 0;
	IntIterator       currentPathIt;
	Term              currentSubTerm    = null;
	
	private PIOPathIteratorImpl               () {
	    currentPathIt = posInTerm ().iterator ();
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
	    pio = new PosInOccurrence ( cfma,
		    posInTerm.firstN(count - 1),
		    inAntec );            

        
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
	    else {
		res           =  -1 ;
		currentPathIt = null;
	    }

	    child = res;
	    ++count;
	    return res;
	}
    }
	
}