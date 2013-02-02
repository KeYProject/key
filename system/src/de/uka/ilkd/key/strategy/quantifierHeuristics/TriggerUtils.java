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



package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;

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
    public static Iterator<Term> iteratorByOperator(Term term, Operator op) {
        return setByOperator ( term, op ).iterator ();
    }

    public static ImmutableSet<Term> setByOperator(Term term, Operator op) {
        if ( term.op () == op )
            return setByOperator ( term.sub ( 0 ), op )
                   .union ( setByOperator ( term.sub ( 1 ), op ) );
        return DefaultImmutableSet.<Term>nil().add ( term );
    }


    /**
     * 
     * @param set0
     * @param set1
     * @return a set of quantifiableVariable which are belonged to 
     *          both set0 and set1 have
     */
    public static ImmutableSet<QuantifiableVariable> intersect(ImmutableSet<QuantifiableVariable> set0,
                                                      ImmutableSet<QuantifiableVariable> set1) {
        ImmutableSet<QuantifiableVariable> res = DefaultImmutableSet.<QuantifiableVariable>nil();
        for (QuantifiableVariable aSet0 : set0) {
            final QuantifiableVariable el = aSet0;
            if (set1.contains(el)) res = res.add(el);
        }
        return res;
    }
    
    public static boolean isTrueOrFalse(Term res) {
        final Operator op = res.op ();
        return op == Junctor.TRUE || op == Junctor.FALSE;
    }
}
