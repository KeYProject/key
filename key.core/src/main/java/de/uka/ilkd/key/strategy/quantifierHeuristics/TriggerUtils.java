/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

class TriggerUtils {

    /**
     * remove all the quantifiable variable bounded in the top level of a given formula.
     */
    public static Term discardQuantifiers(Term qterm) {
        Term t = qterm;
        while (t.op() instanceof Quantifier) {
            t = t.sub(0);
        }
        return t;
    }

    /**
     * @return set of terms that are that the term splite d through the operator <code>op</code>
     */
    public static Iterator<Term> iteratorByOperator(Term term, Operator op) {
        return setByOperator(term, op).iterator();
    }

    public static ImmutableSet<Term> setByOperator(Term term, Operator op) {
        if (term.op() == op) {
            return setByOperator(term.sub(0), op).union(setByOperator(term.sub(1), op));
        }
        return DefaultImmutableSet.<Term>nil().add(term);
    }


    /**
     *
     * @param set0
     * @param set1
     * @return a set of quantifiableVariable which are belonged to both set0 and set1 have
     */
    public static ImmutableSet<QuantifiableVariable> intersect(
            ImmutableSet<QuantifiableVariable> set0, ImmutableSet<QuantifiableVariable> set1) {
        ImmutableSet<QuantifiableVariable> res = DefaultImmutableSet.nil();
        for (QuantifiableVariable aSet0 : set0) {
            final QuantifiableVariable el = aSet0;
            if (set1.contains(el)) {
                res = res.add(el);
            }
        }
        return res;
    }

    public static boolean isTrueOrFalse(Term res) {
        final Operator op = res.op();
        return op == Junctor.TRUE || op == Junctor.FALSE;
    }
}
