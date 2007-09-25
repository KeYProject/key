package de.uka.ilkd.key.lang.common.operator;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Represents a logic symbol.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IOperator extends Operator, Named {
        /**
         * Checks whether the top level structure of the given {@link Term}
         * is syntactically valid, given the assumption that the top level
         * operator of the term is the same as this Operator. The
         * assumption that the top level operator and the term are equal
         * is NOT checked.  
         * @return true iff the top level structure of the {@link Term} is valid.
         */
        boolean validTopLevel(Term term);

        /**
         * Determines the sort of the {@link Term} if it would be created using this
         * operator as top level operator and the given terms as sub terms. The
         * assumption that the constructed term would be allowed is not checked.
         * @param term an array of Term containing the subterms of a (potential)
         *      term with this operator as top level operator
         * @return sort of the term with this operator as top level operator of the 
         *      given substerms
         */
        Sort sort(Term[] term);


        /**
         * Returns the arity of this operator.  
         * @return 
         */
        int arity();        
}
