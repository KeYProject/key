// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** Meta operators decompose the accT predicate
 * to the subterms of a function application.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public final class MetaAccTArgs extends AsmMetaOperator {


    /** creates a new meta operator. Only one instance is required, so
     * this class may be a singleton. */
    public MetaAccTArgs() {
        super("Base.#ACCT_ARGS", Sort.FORMULA,
              new Sort[] { null, null});
    }


    /** Expects one term with 1 subterm accT(s in f(t1, ..., tn));
     * @return accT(s in t1) or ... or accT(s in tn)
     */
    public Term calculate(Term term, SVInstantiations svInst) {
        // Term term1 = term.sub(0);
// 	Term term2 = term.sub(1);
//         Term result;

// 	if(term2.arity() == 0) {
// 	    result = tf.createJunctorTerm(Op.FALSE);
// 	} else if (term2.arity() == 1) {
// 	    result = tf.createAccTTerm(term1,term2.sub(0));
// 	} else {
// 	    result = tf.createJunctorTerm(Op.OR,
// 					  tf.createAccTTerm(term1,term2.sub(0)),
// 					  tf.createAccTTerm(term1,term2.sub(1)));
// 	    for (int i = 2; i < term2.arity(); ++i) {
// 		result =
// 		    tf.createJunctorTerm(Op.OR, result,tf.createAccTTerm(term1, term2.sub(i)));
// 	    }
// 	}
// 	return result;
	return null;
    }

}
