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



/** Meta operator: do the #phi[[n]] transformation. 
 *
 * @author Stanislas Nanchen
 */

public final class MetaTimed extends AsmMetaOperator {

  
    public MetaTimed() {
	super("#TIMED", Sort.FORMULA,
              new Sort[] { null, null });
    }

    
    /** Expects a term with two subterms 'f(s1, s2, ...)' and 
     * a term t, compute f^t (s1^t, ..., sn^t) if f is dynamic
     * and f (s1^t, ..., sn^t) if f is static.
     */
    public Term calculate(Term term, SVInstantiations svInst) {
        // Term s = term.sub(0);
//         Term t = term.sub(1);
//         Term result;

// 	if (term.op() instanceof NonRigidFunction) {
	    
// 	} else {
	    
// 	}

// 	if(s.arity() == 0) {
// 	    result = tf.createJunctorTerm(Op.TRUE);
// 	} else if (s.arity() == 1) {
// 	    result = tf.createEqualityTerm(s.sub(0), t.sub(0));
// 	} else {
// 	    result = tf.createJunctorTerm(Op.AND,
// 					  tf.createEqualityTerm(s.sub(0), t.sub(0)),
// 					  tf.createEqualityTerm(s.sub(1), t.sub(1)));
// 	    for (int i = 0; i < s.arity(); ++i) {
// 		result = tf.createJunctorTerm(Op.AND, result, tf.createEqualityTerm(s.sub(i), t.sub(i)));
// 	    }
// 	}
//         return result;
	return null;
    }
}
