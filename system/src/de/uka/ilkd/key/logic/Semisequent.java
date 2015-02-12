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
public class Semisequent implements Iterable<SequentFormula> {

    /** the empty semisequent (using singleton pattern) */
    public static final Semisequent EMPTY_SEMISEQUENT = new Empty();
    /** list with the Constraintformulae of the Semisequent */
    private final ImmutableList<SequentFormula> seqList; 
 
    /** used by inner class Empty*/
    private Semisequent() {
        seqList = ImmutableSLList.<SequentFormula>nil(); 
    }


    /** creates a new Semisequent with the Semisequent elements in
     * seqList */ 
    private Semisequent(ImmutableList<SequentFormula> seqList) {
        assert !seqList.isEmpty();
        this.seqList = seqList;
    }
    

    /** creates a new Semisequent with the Semisequent elements in
     * seqList */ 
    public Semisequent(SequentFormula seqFormula) {
        assert seqFormula != null;
        this.seqList = ImmutableSLList.<SequentFormula>nil().append(seqFormula);
    }
    

    /** inserts an element at a specified index performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param idx int encoding the place the element has to be put	
     * @param conForm SequentFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */    
    public SemisequentChangeInfo insert(int idx, SequentFormula conForm) {	
	return removeRedundance(idx, conForm);
    }

    /** inserts the elements of the list at the specified index
     * performing redundancy checks
     * @param idx int encoding the place where the insertion starts
     * @param insertionList IList<SequentFormula> to be inserted
     * starting at idx
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */    
    public SemisequentChangeInfo insert(int idx, ImmutableList<SequentFormula> insertionList) {	
	return removeRedundance(idx, insertionList);
    }

    /** inserts element at index 0 performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param conForm SequentFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(SequentFormula conForm) {
	return insert(0,conForm);
    }

    /** 
     * inserts element at index 0 performing redundancy
     * checks, this may result in returning same semisequent if
     * inserting would create redundancies 
     * @param insertions IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo insertFirst(ImmutableList<SequentFormula> insertions) {
	return insert(0, insertions);
    }
    
    /** inserts element at the end of the semisequent performing
     * redundancy checks, this may result in returning same
     * semisequent if inserting would create redundancies 
     * @param conForm SequentFormula to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */	
    public SemisequentChangeInfo insertLast(SequentFormula conForm) {
	return insert(size(), conForm);
    }

    /** 
     * inserts the formulas of the list at the end of the semisequent
     * performing redundancy checks, this may result in returning same 
     * semisequent if inserting would create redundancies 
     * @param insertions the IList<SequentFormula> to be inserted
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */	
    public SemisequentChangeInfo insertLast(ImmutableList<SequentFormula> insertions) {
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
     * inserts new SequentFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundanceHelp(int idx, 
						       SequentFormula conForm,
						       SemisequentChangeInfo semiCI) {
	return removeRedundanceHelp ( idx, conForm, semiCI, null );
    }

    /** .
     * inserts new SequentFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @param fci null if the formula to be added is new, otherwise an
     * object telling which formula is replaced with the new formula
     * <code>conForm</code>, and what are the differences between the
     * two formulas
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundanceHelp(int idx, 
						       SequentFormula conForm,
						       SemisequentChangeInfo semiCI,
						       FormulaChangeInfo fci) {

	// Search for equivalent formulas and weakest constraint
	ImmutableList<SequentFormula> searchList = semiCI.getFormulaList();
	ImmutableList<SequentFormula> newSeqList = ImmutableSLList.<SequentFormula>nil();
	SequentFormula       cf;
	int                      pos        = -1;

	while ( !searchList.isEmpty() ) {
	    ++pos;
	    cf         = searchList.head ();
	    searchList = searchList.tail();

	    if (conForm != null && cf.formula().equalsModRenaming(conForm.formula())) {

	    semiCI.rejectedFormula( cf );
		return semiCI; // semisequent already contains formula

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
     * @param conForm the IList<SequentFormula> to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance
	(int idx, ImmutableList<SequentFormula> conForm, SemisequentChangeInfo sci) {

	int pos = idx;	
	ImmutableList<SequentFormula> oldFormulas = sci.getFormulaList();

        for (SequentFormula aConForm : conForm) {
            sci = removeRedundanceHelp(pos, aConForm, sci);

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
     * @param conForm the IList<SequentFormula> to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    private SemisequentChangeInfo removeRedundance
	(int idx, ImmutableList<SequentFormula> conForm) {
	return removeRedundance(idx, conForm, new SemisequentChangeInfo(seqList));
    }


    /** .
     * inserts new SequentFormula at index idx and removes
     * duplicates, perform simplifications etc.
     * @param conForm the SequentFormula to be inserted at position idx
     * @param idx an int that means insert conForm at the idx-th
     * position in the semisequent 
     * @return new Semisequent with conForm at index idx and removed
     * redundancies 
     */
    private SemisequentChangeInfo removeRedundance(int idx, 
						   SequentFormula conForm) {
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
     *            the SequentFormula replacing the old element at index idx
     * @return a semi sequent change information object with the new semisequent
     *         and information which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos,
					 SequentFormula conForm) {	
	final int idx = indexOf(pos.constrainedFormula());
	final FormulaChangeInfo fci = new FormulaChangeInfo ( pos, conForm );
	return complete(removeRedundanceHelp(idx, conForm, remove(idx), fci));
    }
    
    /**
     * replaces the <tt>idx</tt>-th formula by <tt>conForm</tt>
     * @param idx the int with the position of the formula to be replaced
     * @param conForm the SequentFormula replacing the formula at the given position
     * @return a SemisequentChangeInfo containing the new sequent and a diff to the old
     *  one
     */
    public SemisequentChangeInfo replace(int idx, SequentFormula conForm) {	
        return complete(removeRedundanceHelp(idx, conForm, remove(idx)));
    }

    /** 
     * replaces the element at place idx with the first element of the
     * given list and adds the rest of the list to the semisequent
     * behind the replaced formula
     * @param pos the formula to be replaced
     * @param replacements the IList<SequentFormula> whose head
     * replaces the element at index idx and the tail is added to the
     * semisequent 
     * @return a semi sequent change information object with the new semisequent
     * and information which formulas have been added or removed
     */
    public SemisequentChangeInfo replace(PosInOccurrence pos,
					 ImmutableList<SequentFormula> replacements) {	
	final int idx = indexOf(pos.constrainedFormula());
	return removeRedundance(idx, replacements, remove(idx));
    }

    public SemisequentChangeInfo replace(int idx, ImmutableList<SequentFormula> replacements) {	
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
        
      final ImmutableList<SequentFormula> formulaList = semiCI.getFormulaList();
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

	ImmutableList<SequentFormula> newList = seqList;  
	ImmutableList<SequentFormula> queue =
	    ImmutableSLList.<SequentFormula>nil();  
	int index = 0;
	
	if (idx<0 || idx>=size()) {
	  return complete(new SemisequentChangeInfo(seqList));
	}


        final SequentFormula[] temp = new SequentFormula[idx];

	while (index<idx) {// go to idx 
	    temp[index] = newList.head();
	    newList=newList.tail();
	    index++;
	}
        
        for (int k=index-1; k>=0; k--) queue=queue.prepend(temp[k]);


	// remove the element that is at head of newList	
	final SequentFormula removedFormula = newList.head();
	newList=newList.tail();
	newList=newList.prepend(queue);
	
	// create change info object
	final SemisequentChangeInfo sci = new SemisequentChangeInfo(newList);
	sci.removedFormula(idx, removedFormula);

	return complete(sci);
    }

    /**
     * returns index of a SequentFormula. An identity check ('==')
     * is used when searching for the SequentFormula, NOT equals on
     * SequentFormula, because a ConstrainedFormulae identifies the origin
     * of a formula.
     * @param conForm the SequentFormula the index want to be
     * determined 
     * @return index of conForm (-1 if not found)
     */
    public int indexOf(SequentFormula conForm) {
	ImmutableList<SequentFormula> searchList = seqList;  
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
     * @return SequentFormula found at index idx
     * @throws IndexOutOfBoundsException if idx is negative or 
     * greater or equal to {@link Sequent#size()}
     */
    public SequentFormula get(int idx) {        
	if (idx < 0 || idx >= seqList.size()) {
	    throw new IndexOutOfBoundsException();
	}
        return seqList.take(idx).head();	
    }

    /** @return the first SequentFormula of this Semisequent */
    public SequentFormula getFirst() {
	return seqList.head();
    }

    /** checks if a SequentFormula is in this Semisequent
     * (identity check)
     * @param conForm the ConstraintForumla to look for
     * @return true iff. conForm has been found in this
     * Semisequent 
     */
    public boolean contains(SequentFormula conForm) {
	return indexOf(conForm)!=-1;
    }
    
    /** checks if a SequentFormula is in this Semisequent
     * (equality check)
     * @param conForm the ConstraintForumla to look for
     * @return true iff. conForm has been found in this
     * Semisequent 
     */
    public boolean containsEqual(SequentFormula conForm) {
	return seqList.contains(conForm);        
    }

    /** 
     * returns iterator about the elements of the sequent     
     * @return Iterator<SequentFormula>
     */
    public Iterator<SequentFormula> iterator() {
	return seqList.iterator();
    }

    public ImmutableList<SequentFormula> toList () {
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
	 * @param conForm SequentFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo insert(int idx, SequentFormula conForm) {	
	    return insertFirst(conForm);
	}

	/** inserts the element at index 0
	 * @param conForm SequentFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo insertFirst(SequentFormula conForm) {
	  final SemisequentChangeInfo sci = new SemisequentChangeInfo
	  (ImmutableSLList.<SequentFormula>nil().prepend(conForm));
	  sci.addedFormula(0, conForm);
	  return complete(sci);
	}

	/** inserts the element at the end of the semisequent
	 * @param conForm SequentFormula to be inserted
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */	
	public SemisequentChangeInfo insertLast(SequentFormula conForm) {
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
	 * @param conForm the SequentFormula replacing the old
	 * element at index idx
	 * @return semisequent change information object with new semisequent
	 * with conForm at place idx 
	 */
	public SemisequentChangeInfo replace(int idx, SequentFormula conForm) {
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
	  return complete(new SemisequentChangeInfo(ImmutableSLList.<SequentFormula>nil()));
	}

	/** returns index of a SequentFormula 
	 * @param conForm the SequentFormula the index want to be
	 * determined 
	 * @return index of conForm
	 */
	public int indexOf(SequentFormula conForm) {
	    return -1;
	}

	/** gets the element at a specific index
	 * @param idx int representing the index of the element we
	 * want to have
	 * @return SequentFormula found at index idx
	 */
	public SequentFormula get(int idx) {
	    return null;
	}

	/** @return the first SequentFormula of this Semisequent 
	 */
	public SequentFormula getFirst() {
	    return null;
	}
        
	/** checks if a SequentFormula is in this Semisequent
	 * @param conForm the ConstraintForumla to look for
	 * @return true iff. conForm has been found in this
	 * Semisequent 
	 */
	public boolean contains(SequentFormula conForm) {
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
