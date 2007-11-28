// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SetAsListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;

class TriggerUtils {

    /**
     * remove all the quantifiable variable bounded in the top level 
     * of a given formula.
     */
    public static Term discardQuantifiers(Term qterm) {
        Term t = qterm;
        while ( t.op () instanceof Quantifier )
            t = t.sub ( 0 );
        return t;
    }
    
    /**
     * @return set of terms that are that the term splite d through the operator
     *         <code>op</code>
     */
    public static IteratorOfTerm iteratorByOperator(Term term, Operator op) {
        return setByOperator ( term, op ).iterator ();
    }

    public static SetOfTerm setByOperator(Term term, Operator op) {
        if ( term.op () == op )
            return setByOperator ( term.sub ( 0 ), op )
                   .union ( setByOperator ( term.sub ( 1 ), op ) );
        return SetAsListOfTerm.EMPTY_SET.add ( term );
    }


    /**
     * 
     * @param set0
     * @param set1
     * @return a set of quantifiableVariable which are belonged to 
     *          both set0 and set1 have
     */
    public static SetOfQuantifiableVariable intersect(SetOfQuantifiableVariable set0,
                                                      SetOfQuantifiableVariable set1) {
        SetOfQuantifiableVariable res = SetAsListOfQuantifiableVariable.EMPTY_SET;
        final IteratorOfQuantifiableVariable it = set0.iterator ();
        while ( it.hasNext () ) {
            final QuantifiableVariable el = it.next ();
            if ( set1.contains ( el ) ) res = res.add ( el );
        }
        return res;
    }
    
    public static boolean isTrueOrFalse(Term res) {
        final Operator op = res.op ();
        return op == Op.TRUE || op == Op.FALSE;
    }
}
