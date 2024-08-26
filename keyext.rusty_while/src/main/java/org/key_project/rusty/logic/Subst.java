/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.logic.op.BoundVariable;
import org.key_project.rusty.logic.op.LogicVariable;
import org.key_project.util.collection.ImmutableArray;

public class Subst {
    private final BoundVariable v;
    private final Term s;
    private final TermBuilder tb;

    private int index = 1;

    public Subst(BoundVariable v, Term sub, TermBuilder tb) {
        this.v = v;
        this.s = sub;
        this.tb = tb;
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>.
     */
    public Term apply(Term t) {
        return apply1(t);
    }

    /**
     * substitute <code>s</code> for <code>v</code> in <code>t</code>.
     */
    protected Term apply1(Term t) {
        if (t.op() instanceof LogicVariable lv && lv.getIndex() == index) {
            return s;
        } else {
            return applyOnSubterms(t);
        }
    }

    /**
     * substitute <code>s</code> for <code>v</code> in every subterm of <code>t</code>, and build a
     * new term. It is assumed, that one of the subterms contains a free occurrence of
     * <code>v</code>, and that the case <code>v==t<code> is already handled.
     */
    private Term applyOnSubterms(Term t) {
        final int arity = t.arity();
        final Term[] newSubterms = new Term[arity];
        for (int i = 0; i < arity; i++) {
            applyOnSubterm(t, i, newSubterms);
        }
        return tb.tf().createTerm(t.op(), newSubterms,
            (ImmutableArray<QuantifiableVariable>) t.boundVars());
    }

    /**
     * Apply the substitution of the subterm <code>subtermIndex</code> of term/formula
     * <code>completeTerm</code>. The result is stored in <code>newSubterms</code> and
     * <code>newBoundVars</code> (at index <code>subtermIndex</code>)
     */
    protected void applyOnSubterm(Term completeTerm, int subtermIndex, Term[] newSubterms) {
        var oldIndex = index;
        if (completeTerm.op().bindVarsAt(subtermIndex)) {
            index += completeTerm.varsBoundHere(subtermIndex).size();
        }
        newSubterms[subtermIndex] = apply1(completeTerm.sub(subtermIndex));

        index = oldIndex;
    }

    protected static ImmutableArray<QuantifiableVariable> getSingleArray(
            ImmutableArray<QuantifiableVariable>[] bv) {
        if (bv == null) {
            return null;
        }
        ImmutableArray<QuantifiableVariable> result = null;
        for (ImmutableArray<QuantifiableVariable> arr : bv) {
            if (arr != null && !arr.isEmpty()) {
                if (result == null) {
                    result = arr;
                } else {
                    assert arr.equals(result) : "expected: " + result + "\nfound: " + arr;
                }
            }
        }
        return result;
    }
}
