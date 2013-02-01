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


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;


/** 
 * All symbols acting as members of a term e.g. logical operators, predicates, 
 * functions, variables etc. have to implement this interface.  
 */
public interface Operator extends Named, SVSubstitute {
    
    /**
     * the arity of this operator  
     */
    int arity();
    

    /**
     * Determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param terms an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    Sort sort(ImmutableArray<Term> terms);
    
    
    /**
     * Tells whether the operator binds variables at the n-th subterm.
     */
    boolean bindVarsAt(int n);
    
    
    /**
     * Tells whether the operator is rigid.
     */
    boolean isRigid();      
    
    
    /**
     * Checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the {@link Term} is valid.
     */
    boolean validTopLevel(Term term);
    
    
    /**
     * Tests if this operator (plays role of a template) matches 
     * the given operator with respect to the given match 
     * conditions. 
     * If matching fails <code>null</code> is returned.
     * @param subst the Operator to match 
     * @param mc the MatchConditions to pay respect to
     * @param services the Services to access model information
     * @return the resulting match conditions (e.g. with new added
     * instantiations of schema variables)
     */
    MatchConditions match(SVSubstitute subst, 
	                  MatchConditions mc, 
	                  Services services); 
}
