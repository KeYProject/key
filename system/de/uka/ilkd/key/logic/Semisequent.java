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

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;


/** 
 * This class represents the succedent or antecendent part of a
 * sequent. It is more or less a list without duplicates and subsumed
 * formulas. This is ensured using method removeRedundancy. In future
 * versions it can be enhanced to do other simplifications. A sequent
 * and so a semisequent has to be immutable. 
 */
public class Semisequent implements Iterable<ConstrainedFormula> {

    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();
    /** list with the Constraintformulae of the Semisequent */
    private final ImmutableList<ConstrainedFormula> seqList; 
 
    /** used by inner class Empty*/
    private Semisequent() {
        seqList = ImmutableSLList.<ConstrainedFormula>nil(); 
    }


    /** creates a new Semisequent with the Semisequent elements in
     * seqList */ 
    private Semisequent(ImmutableList<ConstrainedFormula> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }
    

    /** inserts an element at a specified index performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param idx int encoding the place the element has to be put	
     * @param conForm ConstrainedFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */    
    public SemisequentChangeInfo insert(int idx, ConstrainedFormula conForm) {	
	return removeRedundance(idx, conForm);
    }

    /** inserts the elements of the list at the specified index
     * performing redundancy checks
     * @param idx int encoding the place where the insertion starts
     * @param insertionList IList<ConstrainedFormula> to be inserted
     * starting at idx
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */    
    public SemisequentChangeInfo insert(int idx, ImmutableList<ConstrainedFormula> insertionList) {	
	return removeRedundance(idx, insertionList);
    }

    /** inserts element at index 0 performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param conForm ConstrainedFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(ConstrainedFormula conForm) {
	return insert(0,conForm);
    }

    /** 
     * inserts element at index 0 performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param insertions IList<ConstrainedFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(ImmutableList<ConstrainedFormula> insertions) {
	return insert(0, insertions);
    }
    
    /** inserts element at the end of the semisequent performing
     * redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies 
     * @param conForm ConstrainedFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */	
    public SemisequentChangeInfo insertLast(ConstrainedFormula conForm) {
	return insert(size(), conForm);
    }

    /** 
     * inserts the formulas of the list at the end of the semisequent
     * performing redundancy checks, this may result in returning same 
     * semisequent if inserting would create redundancies 
     * @param insertions the IList<ConstrainedFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */	
    public SemisequentChangeInfo insertLast(ImmutableList<ConstrainedFormula> insertions) {
	return insert(size(), insertions);
    }

    /**
     * is this a semisequent that contains no formulas
     * @return true if the semisequent contains no formulas
     */
    public boolean isEmpty() {
        return seqList.isEmpty();
    }

    
    /** .
     * inserts new ConstrainedFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundanceHelp(int idx, 
						       ConstrainedFormula conForm,
						       SemisequentChangeInfo semiCI) {
	return removeRedundanceHelp ( idx, conForm, semiCI, null );
    }

    /** .
     * inserts new ConstrainedFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @param fci null if the formula to be added is new, otherwise an
     * object telling which formula is replaced with the new formula
     * <code>conForm</code>, and what are the differences between the
     * two formulas
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundanceHelp(int idx, 
						       ConstrainedFormula conForm,
						       SemisequentChangeInfo semiCI,
						       FormulaChangeInfo fci) {

	// Search for equivalent formulas and weakest constraint
	ImmutableList<ConstrainedFormula> searchList = semiCI.getFormulaList();
	ImmutableList<ConstrainedFormula> newSeqList = ImmutableSLList.<ConstrainedFormula>nil();
	ConstrainedFormula       cf;
	Constraint               c;
	int                      pos        = -1;

	while ( !searchList.isEmpty() ) {
	    ++pos;
	    cf         = searchList.head ();
	    searchList = searchList.tail();	    

            // for the moment we do not remove redundancy if intersection sorts are required
            // Attention: just replacing null by new Services () slows KeY down by factor 3
	    c          = Constraint.BOTTOM.unify ( cf     .formula (),
						   conForm.formula (), 
                                                   null );
            
	    
	    if ( c.isAsWeakAs ( cf     .constraint () ) ||
		 c.isAsWeakAs ( conForm.constraint () ) ) {
		if ( cf.constraint ().isAsWeakAs   ( conForm.constraint () ) ) {		  
		    semiCI.rejectedFormula( cf );
                    return semiCI; // semisequent already contains formula
		} else if ( cf.constraint ().isAsStrongAs 
			    ( conForm.constraint () ) ) {                  
                    semiCI.removedFormula(pos, cf);
		    if ( idx > pos )
			--idx;
		    --pos;			
		    continue;          // formula of the semisequent can be removed
		}
	    }
	    newSeqList = newSeqList.prepend ( cf );	    	    
	}           

	
	// compose resulting formula list
	if ( fci == null )
	    semiCI.addedFormula(idx, conForm);
	else
	    semiCI.modifiedFormula(idx, fci);

	if ( idx > pos ) {
	    searchList = searchList.prepend ( conForm );
	}

	while ( !newSeqList.isEmpty() ) {
	    searchList = searchList.prepend ( newSeqList.head () );
	    newSeqList = newSeqList.tail ();
	    if ( idx == pos ) {
		searchList = searchList.prepend ( conForm );
	    }
	    --pos;
	}      

	// add new formula list to result object
	semiCI.setFormulaList ( searchList );

	return semiCI;
    }

    /** .
     * inserts new ConstrainedFormulas starting at index idx and removes
     * duplicates, perform simplifications etc.
     * @param conForm the IList<ConstrainedFormula> to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance
	(int idx, ImmutableList<ConstrainedFormula> conForm, SemisequentChangeInfo sci) {

	int pos = idx;	
	ImmutableList<ConstrainedFormula> oldFormulas = sci.getFormulaList();
	final Iterator<ConstrainedFormula> it = conForm.iterator();	

	while (it.hasNext()) {	   
	    sci = removeRedundanceHelp(pos, it.next(), sci);
            
	    if (sci.getFormulaList() != oldFormulas) {
		pos = sci.getIndex() + 1;
		oldFormulas = sci.getFormulaList();
	    }
	}	

	return complete(sci);
    }

    /** .
     * inserts new ConstrainedFormulas starting at index idx and removes
     * duplicates, perform simplifications etc.
     * @param conForm the IList<ConstrainedFormula> to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance
	(int idx, ImmutableList<ConstrainedFormula> conForm) {
	return removeRedundance(idx, conForm, new SemisequentChangeInfo(seqList));
    }


    /** .
     * inserts new ConstrainedFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @param conForm the ConstrainedFormula to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return new Semisequent with conForm at index idx and removed
     * redundancies 
     */
    private SemisequentChangeInfo removeRedundance(int idx, 
						   ConstrainedFormula conForm) {
	return complete
	    (removeRedundanceHelp(idx, conForm, 
				  new SemisequentChangeInfo(seqList)));
    }


    /**
     * replaces the element at place idx with conForm
     * 
     * @param pos
     *            the PosInOccurrence describing the position of and within the
     *            formula below which the formula differs from the new formula
     *            <code>conForm</code>
     * @param conForm
     *            the ConstrainedFormula replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos,
					 ConstrainedFormula conForm) {	
	final int idx = indexOf(pos.constrainedFormula());
	final FormulaChangeInfo fci = new FormulaChangeInfo ( pos, conForm );
	return complete(removeRedundanceHelp(idx, conForm, remove(idx), fci));
    }
    
    /**
     * replaces the <tt>idx</tt>-th formula by <tt>conForm</tt>
     * @param idx the int with the position of the formula to be replaced
     * @param conForm the ConstrainedFormula replacing the formula at the given position
     * @return a SemisequentChangeInfo containing the new sequent and a diff to the old
     *  one
     */
    public SemisequentChangeInfo replace(int idx, ConstrainedFormula conForm) {	
        return complete(removeRedundanceHelp(idx, conForm, remove(idx)));
    }

    /** 
     * replaces the element at place idx with the first element of the
     * given list and adds the rest of the list to the semisequent
     * behind the replaced formula
     * @param pos the formula to be replaced
     * @param replacements the IList<ConstrainedFormula> whose head
     * replaces the element at index idx and the tail is added to the
     * semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos,
					 ImmutableList<ConstrainedFormula> replacements) {	
	final int idx = indexOf(pos.constrainedFormula());
	return removeRedundance(idx, replacements, remove(idx));
    }

    public SemisequentChangeInfo replace(int idx, ImmutableList<ConstrainedFormula> replacements) {	
	return removeRedundance(idx, replacements, remove(idx));
    }

    /** @return int counting the elements of this semisequent */
    public int size() {
	return seqList.size();
    }

    /** 
     * creates a semisequent out of the semisequent change info (semiCI)
     * object and hands it over to semiCI 
     */
    protected SemisequentChangeInfo complete(SemisequentChangeInfo semiCI)
    {
        
      final ImmutableList<ConstrainedFormula> formulaList = semiCI.getFormulaList();
      if (formulaList.isEmpty()) {
          semiCI.setSemisequent(EMPTY_SEMISEQUENT);
      } else {
          final Semisequent result = formulaList == seqList ? 
                  this : new Semisequent(formulaList);
          semiCI.setSemisequent(result);
      }
      return semiCI;
    }

      
    /** 
     * removes an element 
     * @param idx int being the index of the element that has to
     * be removed
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo remove(int idx) {	       

	ImmutableList<ConstrainedFormula> newList = seqList;  
	ImmutableList<ConstrainedFormula> queue =
	    ImmutableSLList.<ConstrainedFormula>nil();  
	int index = 0;
	
	if (idx<0 || idx>=size()) {
	  return complete(new SemisequentChangeInfo(seqList));
	}


        final ConstrainedFormula[] temp = new ConstrainedFormula[idx];

	while (index<idx) {// go to idx 
	    temp[index] = newList.head();
	    newList=newList.tail();
	    index++;
	}
        
        for (int k=index-1; k>=0; k--) queue=queue.prepend(temp[k]);


	// remove the element that is at head of newList	
	final ConstrainedFormula removedFormula = newList.head();
	newList=newList.tail();
	newList=newList.prepend(queue);
	
	// create change info object
	final SemisequentChangeInfo sci = new SemisequentChangeInfo(newList);
	sci.removedFormula(idx, removedFormula);

	return complete(sci);
    }

    /**
     * returns index of a ConstrainedFormula. An identity check ('==')
     * is used when searching for the ConstrainedFormula, NOT equals on
     * ConstrainedFormula, because a ConstrainedFormulae identifies the origin
     * of a formula.
     * @param conForm the ConstrainedFormula the index want to be
     * determined 
     * @return index of conForm (-1 if not found)
     */
    public int indexOf(ConstrainedFormula conForm) {
	ImmutableList<ConstrainedFormula> searchList = seqList;  
	int index=0;
	while (!searchList.isEmpty())
	    { 
		if (searchList.head()==conForm) {
		    return index;
		} else {
		    index++;
		}
		searchList=searchList.tail();
	    } 
	return -1;
    }

    /** gets the element at a specific index
     * @param idx int representing the index of the element we
     * want to have
     * @return ConstrainedFormula found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or 
     * greater or equal to {@link Sequent#size()}
     */
    public ConstrainedFormula get(int idx) {        
	if (idx < 0 || idx >= seqList.size()) {
	    throw new IndexOutOfBoundsException();
	}
        return seqList.take(idx).head();	
    }

    /** @return the first ConstrainedFormula of this Semisequent */
    public ConstrainedFormula getFirst() {
	return seqList.head();
    }

    /** checks if a ConstrainedFormula is in this Semisequent
     * (identity check)
     * @param conForm the ConstraintForumla to look for
     * @return true iff. conForm has been found in this
     * Semisequent 
     */
    public boolean contains(ConstrainedFormula conForm) {
	return indexOf(conForm)!=-1;
    }
    
    /** checks if a ConstrainedFormula is in this Semisequent
     * (equality check)
     * @param conForm the ConstraintForumla to look for
     * @return true iff. conForm has been found in this
     * Semisequent 
     */
    public boolean containsEqual(ConstrainedFormula conForm) {
	return seqList.contains(conForm);        
    }

    /** 
     * returns iterator about the elements of the sequent     
     * @return Iterator<ConstrainedFormula>
     */
    public Iterator<ConstrainedFormula> iterator() {
	return seqList.iterator();
    }

    public ImmutableList<ConstrainedFormula> toList () {
	return seqList;
    }

    public boolean equals(Object o) {
 	if ( ! ( o instanceof Semisequent ) ) 
	    return false;
	return seqList.equals(((Semisequent) o).seqList);
    }

    
    public int hashCode () {
        return seqList.hashCode ();
    }
    

    /** @return String representation of this Semisequent */
    public String toString() {
	return seqList.toString();
    }


    
    // inner class used to represent an empty semisequent 
    private static class Empty extends Semisequent{

	private Empty() {
	    super();
	}
	
	/** inserts the element always at index 0 ignores the first
	 * argument 
	 * @param idx int encoding the place the element has to be put	
	 * @param conForm ConstrainedFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo insert(int idx, ConstrainedFormula conForm) {	
	    return insertFirst(conForm);
	}

	/** inserts the element at index 0
	 * @param conForm ConstrainedFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo insertFirst(ConstrainedFormula conForm) {
	  final SemisequentChangeInfo sci = new SemisequentChangeInfo
	  (ImmutableSLList.<ConstrainedFormula>nil().prepend(conForm));
	  sci.addedFormula(0, conForm);
	  return complete(sci);
	}

	/** inserts the element at the end of the semisequent
	 * @param conForm ConstrainedFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */	
	public SemisequentChangeInfo insertLast(ConstrainedFormula conForm) {
	    return insertFirst(conForm);
	}


        /**
         * is this a semisequent that contains no formulas
         * @return true if the semisequent contains no formulas
         */
        public boolean isEmpty() {
	    return true;
	}

	/** replaces the element at place idx with conForm
	 * @param idx an int specifying the index of the element that
	 * has to be replaced 
	 * @param conForm the ConstrainedFormula replacing the old
	 * element at index idx
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo replace(int idx, ConstrainedFormula conForm) {
	    return insertFirst(conForm);
	}

	/** @return int counting the elements of this semisequent */ 
	public int size() { 
	    return 0; 
	}

	/** removes an element 
	 * @param idx int being the index of the element that has to
	 * be removed
	 * @return semisequent change information object with an empty
	 * semisequent as result
	 */
	public SemisequentChangeInfo remove(int idx) {
	  return complete(new SemisequentChangeInfo(ImmutableSLList.<ConstrainedFormula>nil()));
	}

	/** returns index of a ConstrainedFormula 
	 * @param conForm the ConstrainedFormula the index want to be
	 * determined 
	 * @return index of conForm
	 */
	public int indexOf(ConstrainedFormula conForm) {
	    return -1;
	}

	/** gets the element at a specific index
	 * @param idx int representing the index of the element we
	 * want to have
	 * @return ConstrainedFormula found at index idx
	 */
	public ConstrainedFormula get(int idx) {
	    return null;
	}

	/** @return the first ConstrainedFormula of this Semisequent 
	 */
	public ConstrainedFormula getFirst() {
	    return null;
	}
        
	/** checks if a ConstrainedFormula is in this Semisequent
	 * @param conForm the ConstraintForumla to look for
	 * @return true iff. conForm has been found in this
	 * Semisequent 
	 */
	public boolean contains(ConstrainedFormula conForm) {
	    return false;
	}

	public boolean equals(Object o) {
	    return o == this;
	}

	public int hashCode () {
	    return 34567;
	}
    
	/** @return String representation of this Semisequent */
	public String toString() {
	    return "[]";
	}
    }    
}

