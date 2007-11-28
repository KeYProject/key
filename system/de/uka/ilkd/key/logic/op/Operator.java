// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
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
     * returns the name of the operator 
     * @return name of the operator 
     */
    Name name();

    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the {@link Term} is valid.
     */
    boolean validTopLevel(Term term);

    /**
     * determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param term an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    Sort sort(Term[] term);


    /**
     * the arity of this operator  
     * @return arity of the Operator as int 
     */
    int arity();

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    boolean isRigid (Term term);  

    /**
     * tests if this operator (plays role of a template) matches 
     * the given operator with respect to the given match 
     * conditions. 
     * If matching fails <code>null</code> is returned.
     * @param subst the Operator to match 
     * @param mc the MatchConditions to pay respect to
     * @param services the Services to access model information
     * @return the resulting match conditions (e.g. with new added
     * instantiations of schema variables)
     */
    MatchConditions match(SVSubstitute subst, MatchConditions mc, Services services); 

}
