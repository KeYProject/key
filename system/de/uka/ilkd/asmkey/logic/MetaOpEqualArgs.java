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


/** Meta operator expands equality of two terms on equality of all
 * subterms. This meta operator replaces two terms with arbitrary but
 * equal arity with the conjunction of equalities of all subterms,
 * i.e.  f(s1, s2, s3), g(t1, t2,t3) leads to s1=t1 & s2=t2 & s3=t3.
 *
 * @author Hubert Schmid
 */

public final class MetaOpEqualArgs extends AsmMetaOperator {


    /** creates a new meta operator. Only one instance is required, so
     * this class may be a singleton. */
    public MetaOpEqualArgs() {
        super("Base.#OP_EQ_ARGS", Sort.FORMULA,
              new Sort[] { null, null });
    }


    /** Expects a term with two subterms 'f(s1, s2, ...)' and 'g(t1,
     * t2, ...)'. Returns the conjunctition 's1=t1 & s2=t2 & ... */
    public Term calculate(Term term, SVInstantiations svInst) {
	
        // Term s = term.sub(0);
//         Term t = term.sub(1);

// 	/* defer calculation */
// 	if (t.op() instanceof NArityLogicVariable ||
// 	    s.op() instanceof NArityLogicVariable) {
// 	    return term;
// 	} else {
// 	    if (s.arity() != t.arity()) {
// 		throw new IllegalArgumentException("Terms " + s + " and " + t + " have differnt aritis.");
// 	    }
// 	    Term result;
// 	    if(s.arity() == 0) {
// 		result = tf.createJunctorTerm(Op.TRUE);
// 	    } else if (s.arity() == 1) {
// 		result = tf.createEqualityTerm(s.sub(0), t.sub(0));
// 	    } else {
// 		result = tf.createJunctorTerm(Op.AND,
// 					      tf.createEqualityTerm(s.sub(0), t.sub(0)),
// 					      tf.createEqualityTerm(s.sub(1), t.sub(1)));
// 		for (int i = 0; i < s.arity(); ++i) {
// 		    result = tf.createJunctorTerm(Op.AND, result, tf.createEqualityTerm(s.sub(i), t.sub(i)));
// 		}
// 	    }
// 	    return result;
// 	}
	return null;
    }

}
