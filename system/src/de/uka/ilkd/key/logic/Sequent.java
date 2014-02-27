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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;


/** This class represents a sequent. A sequent consists of an
 * antecedent and succedent. As a sequent is persistent there is no
 * public constructor. 
 * <p>
 * A sequent is created either by using one of 
 * the composition methods, that are 
 * {@link Sequent#createSequent},
 * {@link Sequent#createAnteSequent} and
 * {@link Sequent#createSuccSequent} 
 * or by inserting formulas directly into {@link Sequent#EMPTY_SEQUENT}.
 */ 
public class Sequent implements Iterable<SequentFormula> {

    public static final Sequent EMPTY_SEQUENT = new NILSequent();

    /**
     * creates a new Sequent with empty succedent 
     * @param ante the Semisequent that plays the antecedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    public static Sequent createAnteSequent(Semisequent ante) {
	if (ante.isEmpty()) {
	    return EMPTY_SEQUENT;
        }
        return new Sequent(ante,Semisequent.EMPTY_SEMISEQUENT);
    }
    /**
     * creates a new Sequent 
     * @param ante the Semisequent that plays the antecedent part
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    public static Sequent createSequent(Semisequent ante, Semisequent succ) {
        if (ante.isEmpty() && succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
        return new Sequent(ante, succ);
    }
    
    /**
     * creates a new Sequent with empty antecedent 
     * @param succ the Semisequent that plays the succedent part
     * @return the new sequent or the EMPTY_SEQUENT if both antec and succ
     * are same as EMPTY_SEMISEQUENT
     */
    public static Sequent createSuccSequent(Semisequent succ) {
        if (succ.isEmpty()) {
            return EMPTY_SEQUENT;
        }
	return new Sequent(Semisequent.EMPTY_SEMISEQUENT,succ);
    }    

    private final Semisequent antecedent;

    private final Semisequent succedent;

    /**
     * must only be called by NILSequent
     *
     */
    private Sequent() {
        antecedent = Semisequent.EMPTY_SEMISEQUENT;
        succedent  = Semisequent.EMPTY_SEMISEQUENT;
    }
    
    /** creates new Sequent with antecedence and succedence */
    private Sequent(Semisequent antecedent, Semisequent succedent) {
	assert !antecedent.isEmpty() || !succedent.isEmpty();
        this.antecedent = antecedent;
	this.succedent  = succedent;	
    }

    /** 
     * adds a formula to the antecedent (or succedent) of the
     * sequent. Depending on the value of first the formulas are
     * inserted at the beginning or end of the ante-/succedent.
     *  (NOTICE:Sequent determines 
     * index using identy (==) not equality.)
     * @param cf the SequentFormula to be added
     * @param antec boolean selecting the correct semisequent where to
     * insert the formulas. If set to true, the antecedent is taken
     * otherwise the succedent.
     * @param first boolean if true the formula is added at the
     * beginning of the ante-/succedent, otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(SequentFormula cf, 
					boolean antec, boolean first) {

	final Semisequent seq = antec ? antecedent : succedent;
	
	final SemisequentChangeInfo semiCI = first ? 
	    seq.insertFirst(cf) : seq.insertLast(cf);	

	return SequentChangeInfo.createSequentChangeInfo
	    (antec, semiCI, composeSequent(antec, semiCI.semisequent()), this);	
    }

    /** 
     * adds a formula to the sequent at the given
     * position. (NOTICE:Sequent determines 
     * index using identy (==) not equality.)
     * @param cf a SequentFormula to be added
     * @param p a PosInOccurrence describes position in the sequent 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(SequentFormula cf, 
            PosInOccurrence p) {
	final Semisequent seq = getSemisequent(p);

	final SemisequentChangeInfo semiCI = seq.insert(seq.indexOf(p.constrainedFormula()),cf);
	
	return SequentChangeInfo.createSequentChangeInfo
	    (p.isInAntec(), semiCI, composeSequent(p, semiCI.semisequent()), this);
    }

    /** 
     * adds list of formulas to the antecedent (or succedent) of the
     * sequent. Depending on the value of first the formulas are
     * inserted at the beginning or end of the ante-/succedent.
     *  (NOTICE:Sequent determines 
     * index using identity (==) not equality.)
     * @param insertions the IList<SequentFormula> to be added
     * @param antec boolean selecting the correct semisequent where to
     * insert the formulas. If set to true, the antecedent is taken
     * otherwise the succedent.
     * @param first boolean if true the formulas are added at the
     * beginning of the ante-/succedent, otherwise to the end
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions,
					boolean antec, boolean first) {

	final Semisequent seq = antec ? antecedent : succedent;
	
	final SemisequentChangeInfo semiCI = first ? seq.insertFirst(insertions) :
	    seq.insertLast(insertions);	

	return SequentChangeInfo.createSequentChangeInfo
	    (antec, semiCI, composeSequent(antec, semiCI.semisequent()), this);	
    }

    /** adds the formulas of list insertions to the sequent starting at
     * position p. (NOTICE:Sequent determines 
     * index using identy (==) not equality.)
     * @param insertions a IList<SequentFormula> with the formulas to be added
     * @param p the PosInOccurrence describing the position where to
     * insert the formulas 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo addFormula(ImmutableList<SequentFormula> insertions, 
					PosInOccurrence p) {
	final Semisequent seq = getSemisequent(p);

	final SemisequentChangeInfo semiCI = 
	    seq.insert(seq.indexOf(p.constrainedFormula()), insertions);

	return SequentChangeInfo.createSequentChangeInfo
	    (p.isInAntec(), semiCI, composeSequent(p, semiCI.semisequent()), this);
    }

    /** returns semisequent of the antecedent to work with */
    public Semisequent antecedent() {
	return antecedent;
    }

    /** 
     * replaces the formula at the given position with another one
     * (NOTICE:Sequent determines 
     * index using identity (==) not equality.)  
     * @param newCF the SequentFormula replacing the old one
     * @param p a PosInOccurrence describes position in the sequent 
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo changeFormula(SequentFormula newCF,
					   PosInOccurrence p) { 	
	final SemisequentChangeInfo semiCI = 
            getSemisequent(p).replace(p, newCF);

	return SequentChangeInfo.createSequentChangeInfo
	    (p.isInAntec(), semiCI, composeSequent(p, semiCI.semisequent()), this);
    }

    /** 
     * replaces the formula at position p with the head of the given
     * list and adds the remaining list elements to the sequent
     * (NOTICE:Sequent determines 
     * index using identity (==) not equality.)  
     * @param replacements the IList<SequentFormula> whose head
     * replaces the formula at position p and adds the rest of the list
     * behind the changed formula
     * @param p a PosInOccurrence describing the position of the formula
     * to be replaced
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed 
     */
    public SequentChangeInfo changeFormula(ImmutableList<SequentFormula> replacements,
					   PosInOccurrence p) {

	final SemisequentChangeInfo semiCI = 
            getSemisequent(p).replace(p, replacements);

	final SequentChangeInfo sci = 
            SequentChangeInfo.createSequentChangeInfo
            (p.isInAntec(), semiCI, composeSequent(p, semiCI.semisequent()), this);

	return sci;
    }

    /** returns creates a new sequent out of the current sequent with a
     * replaced antecedent if antec is true, otherwise the succedent is
     * replaced by the given semisequent seq. 
     */
    private Sequent composeSequent(boolean antec, Semisequent seq) {
	if (seq.isEmpty()) {
	    if (!antec && antecedent().isEmpty()) {
	        return EMPTY_SEQUENT;
            } else if (antec && succedent().isEmpty()){
                return EMPTY_SEQUENT;
            }
        }
        return new Sequent(antec ? seq : antecedent(), 
			   antec ? succedent() : seq);
    }

    /** returns new Sequent with replaced antecedent if
     * PosInOccurrence describes a SequentFormula in the antecedent, 
     * the succedent is replaced otherwise. 
     * The new semisequent is seq.
     */
    private Sequent composeSequent(PosInOccurrence p, Semisequent seq) {
	return composeSequent(p.isInAntec(), seq);
    }
    
    /**
     * determines if the sequent is empty.
     * @return true iff the sequent consists of two instances of
     * Semisequent.EMPTY_SEMISEQUENT
     */
    public boolean isEmpty() {
	return antecedent().isEmpty() && succedent().isEmpty();
    }


    public boolean equals(Object o) {
 	if ( ! ( o instanceof Sequent ) ) 
	    return false;
	final Sequent o1 = (Sequent) o;
	return antecedent.equals(o1.antecedent())
	    && succedent.equals(o1.succedent());
    }

    public int formulaNumberInSequent(boolean inAntec,
                                      SequentFormula cfma) {
        int n = inAntec ? 0 : antecedent.size();
        final Iterator<SequentFormula> formIter =
            inAntec ? antecedent.iterator() : succedent.iterator();
        while (formIter.hasNext()) {
            n++;
            if (formIter.next().equals(cfma)) return n;
        }
        throw new RuntimeException("Ghost formula "+cfma+" in sequent "+
                this+" [antec="+inAntec+"]");
    }

    public SequentFormula getFormulabyNr(int formulaNumber) {
        if (formulaNumber <= 0 || formulaNumber>size()) {
            throw new RuntimeException("No formula nr. "+
                    formulaNumber+" in seq. "+this);
        }
        if (formulaNumber<=antecedent.size()) {
            return antecedent.get(formulaNumber - 1);
        }
        return succedent.get((formulaNumber-1)-antecedent.size());
    }

    /** returns the semisequent in which the SequentFormula described
     * by PosInOccurrence p lies
     */
    private Semisequent getSemisequent(PosInOccurrence p) {
	return p.isInAntec() ? antecedent() : succedent();
    }

    public int hashCode () {
        return antecedent.hashCode () * 17 + succedent.hashCode ();
    }


    /** returns iterator about all ConstrainedFormulae of the sequent
     * @return iterator about all ConstrainedFormulae of the sequent
     */
    public Iterator<SequentFormula> iterator() {
	return new SequentIterator( antecedent(), succedent() );
    }


    public boolean numberInAntec(int formulaNumber) {
       return formulaNumber <= antecedent.size();
    }


    /** removes the formula at position p (NOTICE:Sequent determines
     * index using identity (==) not equality.)
     * @param p a PosInOccurrence that describes position in the sequent
     * @return a SequentChangeInfo which contains the new sequent and
     * information which formulas have been added or removed
     */
    public SequentChangeInfo removeFormula(PosInOccurrence p) {
	final Semisequent seq = getSemisequent(p);

	final SemisequentChangeInfo semiCI =
	    seq.remove(seq.indexOf(p.constrainedFormula()));

	final SequentChangeInfo sci = SequentChangeInfo.createSequentChangeInfo
	    (p.isInAntec(), semiCI, composeSequent(p, semiCI.semisequent()), this);

	return sci;
    }

    public int size () {
        return antecedent ().size () + succedent ().size ();
    }

    /** returns semisequent of the succedent to work with */
    public Semisequent succedent() {
	return succedent;
    }

    /** String representation of the sequent
     * @return String representation of the sequent */
    public String toString() {
	return antecedent().toString()+"==>"+succedent().toString();
    }

    /**
     * returns true iff the given variable is bound in a formula of a
     * SequentFormula in this sequent.
     * @param v the bound variable to search for
     */
    public boolean varIsBound(QuantifiableVariable v) {
	final Iterator<SequentFormula> it = iterator();	
	while (it.hasNext()) {
	    final BoundVarsVisitor bvv=new BoundVarsVisitor();
	    it.next().formula().execPostOrder(bvv);
	    if (bvv.getBoundVariables().contains(v)) {
		return true;
	    }
	}
	return false;
    }

    static class NILSequent extends Sequent {
               
        public boolean isEmpty() {
            return true;
        }
                
        public Iterator<SequentFormula> iterator() {
            return ImmutableSLList.<SequentFormula>nil().iterator();
        }
        
        public boolean varIsBound(QuantifiableVariable v) {
            return false;
        }
        
    } 
    
    static class SequentIterator implements Iterator<SequentFormula> {

	private final Iterator<SequentFormula> anteIt;
	private final Iterator<SequentFormula> succIt;      

	SequentIterator(Semisequent ante, 
			Semisequent succ) {
	    this.anteIt = ante.iterator();
	    this.succIt = succ.iterator();            
	}

	public boolean hasNext() {
	    return anteIt.hasNext() || succIt.hasNext();
	}

	public SequentFormula next() {
	    if (anteIt.hasNext()) {
		return anteIt.next();
	    } 	              
	    return succIt.next();
	}

	/** 
         * throw an unsupported operation exception as sequents are immutable
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
    
    /*
     * Returns names of TermLabels, that occur in term or one of its subterms.
     */
    private static Set<Name> getLabelsForTermRecursively(Term term) {
        Set<Name> result = new HashSet<Name>();

        if (term.hasLabels()) {
            for (TermLabel label : term.getLabels()) {
                result.add(label.name());
            }
        }

        for (final Term subTerm : term.subs()) {
            result.addAll(getLabelsForTermRecursively(subTerm));
        }

        return result;
    }

    /*
     * Returns names of TermLabels, that occur in this sequent.
     */
    public Set<Name> getOccuringTermLabels() {
        final Set<Name> result = new HashSet<Name>();
        for (final SequentFormula sf : this) {
            result.addAll(getLabelsForTermRecursively(sf.formula()));
        }
        return result;
    }
}
