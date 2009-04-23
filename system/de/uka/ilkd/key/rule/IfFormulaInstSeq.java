// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.ProofSaver;


/**
 * Instantiation of an if-formula that is a formula of an existing
 * sequent.
 */

public class IfFormulaInstSeq implements IfFormulaInstantiation {

    /**
     * Sequent and formula
     */ 
    private final Sequent            seq;
    private final boolean antec;	// formula is in antecedent?
    private final ConstrainedFormula cf;

    public IfFormulaInstSeq(Sequent p_seq, boolean antec, ConstrainedFormula p_cf ) {
	seq = p_seq;	
        this.antec = antec;
	cf  = p_cf;
    }


    public IfFormulaInstSeq(Sequent seq, int formulaNr ) {
        this(seq, seq.numberInAntec(formulaNr), seq.getFormulabyNr(formulaNr));
    }



    /**
     * @return the cf this is pointing to
     */
    public ConstrainedFormula getConstrainedFormula () {
	return cf;
    }    

    /**
     * Create a list with all formulas of a given semisequent
     */
    private static ListOfIfFormulaInstantiation createListHelp(Sequent     p_s,                                                               
							       boolean antec ) {
	
	ListOfIfFormulaInstantiation res = SLListOfIfFormulaInstantiation.EMPTY_LIST;
	IteratorOfConstrainedFormula  it;
        if (antec) it = p_s.antecedent().iterator ();
           else it = p_s.succedent().iterator ();
	while ( it.hasNext () ) {
	    res = res.prepend(new IfFormulaInstSeq(p_s, antec, it.next()));
	}

	return res;

    }

    public static ListOfIfFormulaInstantiation createList ( Sequent     p_s,                                                            
                                                            boolean antec ) {
        final Semisequent ss = antec ? p_s.antecedent() : p_s.succedent();
        
        synchronized ( cache ) {
            if ( ( antec ? cache.aKey : cache.sKey ) != ss ) {
                final ListOfIfFormulaInstantiation val = createListHelp ( 
		    p_s, antec );
                if ( antec ) {
                    cache.aKey = ss;
                    cache.aVal = val;
                } else {
                    cache.sKey = ss;
                    cache.sVal = val;
                }
            }

            return antec ? cache.aVal : cache.sVal;
        }
    }
        
    public String toString () {       
	return toString(null);
    }
    
    public String toString (Services services) {
        return ProofSaver.printAnything(cf.formula(), services)+
            (cf.constraint().isBottom() ? "" : "<<"+cf.constraint());
    }

    public boolean equals(Object p_obj) {
        if ( ! ( p_obj instanceof IfFormulaInstSeq ) ) {
            return false;
        }
        return seq == ( (IfFormulaInstSeq)p_obj ).seq
               && cf == ( (IfFormulaInstSeq)p_obj ).cf
               && antec == ( (IfFormulaInstSeq)p_obj ).antec;
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + seq.hashCode ();
        result = 37 * result + cf.hashCode ();
        result = 37 * result + ( antec ? 0 : 1 );
        return result;
    }
    
    public boolean inAntec() {
       return antec;
    }

    private PosInOccurrence pioCache = null;
    
    public PosInOccurrence toPosInOccurrence () {
        if (pioCache == null)
            pioCache = new PosInOccurrence ( getConstrainedFormula (),
                                             PosInTerm.TOP_LEVEL,
                                             inAntec () );
        return pioCache;
    }
    
    // a simple cache for the results of the method <code>createList</code>
    private static final class Cache {
        public Semisequent aKey = null;
        public ListOfIfFormulaInstantiation aVal = null;

        public Semisequent sKey = null;
        public ListOfIfFormulaInstantiation sVal = null;
    }
    
    private static final Cache cache = new Cache ();
}
