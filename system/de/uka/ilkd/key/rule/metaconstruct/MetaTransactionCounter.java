// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.JVMIsTransientMethodBuilder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * returns a term representing the static field 
 *   "de.uka.ilkd.key.javacard.KeYJCSystem.<transactionCounter>"
 */
public class MetaTransactionCounter extends MetaField
implements Location {

    public MetaTransactionCounter() {
	super("#transactionCounter", true);
    }

    public boolean isRigid(Term t) {
	return false;
    }

    /**   
     */
    public Sort sort() {
        return METASORT;
    }
    
    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return term.arity() == arity();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Location#mayBeAliasedBy(de.uka.ilkd.key.logic.op.Location)
     */
    public boolean mayBeAliasedBy(Location loc) {       
        return true;
    }
    
    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator
     *    #match(SVSubstitute, 
     *       de.uka.ilkd.key.rule.MatchConditions, 
     *       de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }


    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, 
			  Services services) {	
        return termFactory.createVariableTerm
	    (services.getJavaInfo().getAttribute
	     (JVMIsTransientMethodBuilder.IMPLICIT_TRANSACTION_COUNTER,
	      "de.uka.ilkd.key.javacard.KeYJCSystem"));
    }

}
