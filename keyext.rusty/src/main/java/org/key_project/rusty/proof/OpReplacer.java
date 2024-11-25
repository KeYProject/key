/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.logic.TermFactory;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Replaces operators in a term by other operators with the same signature, or subterms of the term
 * by other terms with the same sort. Does not replace in rusty blocks.
 */
public class OpReplacer {
    /**
     * Term factory.
     */
    private final TermFactory tf;

    /**
     * The replacement map.
     */
    private final ReplacementMap<? extends SyntaxElement, ? extends SyntaxElement> map;

    /**
     * Creates an {@code OpReplacer}.
     *
     * @param map map mapping from the operators/terms to be replaced to the ones to replace them
     *        with.
     * @param tf a term factory.
     */
    public OpReplacer(Map<? extends SyntaxElement, ? extends SyntaxElement> map, TermFactory tf) {
        assert map != null;

        this.map = map instanceof ReplacementMap
                ? (ReplacementMap<? extends SyntaxElement, ? extends SyntaxElement>) map
                : ReplacementMap.create(map);

        this.tf = tf;
    }

    /**
     * <p>
     * Replace a sub-term.
     * </p>
     *
     * @param toReplace the sub-term to replace.
     * @param with the replacement sub-term.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the sub-term replaced.
     */
    public static Term replace(Term toReplace, Term with, Term in, TermFactory tf) {
        Map<Term, Term> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf);
        return or.replace(in);
    }

    /**
     * <p>
     * Replace a sub-term.
     * </p>
     *
     * @param toReplace the sub-term to replace.
     * @param with the replacement sub-term.
     * @param in the terms in which to perform the replacement.
     * @param tf a term factory.
     * @return the terms with all occurences of the sub-term replaced.
     */
    public static ImmutableList<Term> replace(Term toReplace, Term with, ImmutableList<Term> in,
            TermFactory tf) {
        Map<Term, Term> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf);
        return or.replace(in);
    }

    /**
     * <p>
     * Replace an operator.
     * </p>
     *
     * @param toReplace the operator to replace.
     * @param with the replacement operator.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the operator replaced.
     */
    public static Term replace(Operator toReplace, Operator with, Term in, TermFactory tf) {
        Map<Operator, Operator> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf);
        return or.replace(in);
    }

    /**
     * Replaces in an operator.
     *
     * @param op the operator in which to perform the replacement.
     * @return the replaced operator.
     */
    public Operator replace(Operator op) {
        Operator newOp = (Operator) map.get(op);
        if (newOp != null) {
            return newOp;
        } else {
            return op;
        }
    }

    /**
     * Replaces in a term.
     *
     * @param term the term in which to perform the replacement.
     * @return the transformed term.
     */
    public Term replace(Term term) {
        if (term == null) {
            return null;
        }
        final Term newTerm = (Term) map.get(term);
        if (newTerm != null) {
            return newTerm;
        }

        for (SyntaxElement svs : map.keySet()) {
            if (term.equals(svs)) {
                return (Term) map.get(svs);
            }
        }

        final Operator newOp = replace(term.op());

        final int arity = term.arity();
        final Term[] newSubTerms = new Term[arity];
        boolean changedSubTerm = false;
        for (int i = 0; i < arity; i++) {
            Term subTerm = term.sub(i);
            newSubTerms[i] = replace(subTerm);

            if (newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }
        final ImmutableArray<QuantifiableVariable> newBoundVars = replace(term.boundVars());

        final Term result;
        if (newOp != term.op() || changedSubTerm || newBoundVars != term.boundVars()) {
            result =
                tf.createTerm(newOp, newSubTerms, newBoundVars);
        } else {
            result = term;
        }

        return result;
    }

    /**
     * Replaces in a list of terms.
     *
     * @param terms the terms in which to perform the replacement.
     * @return the list of transformed terms.
     */
    public ImmutableList<Term> replace(ImmutableList<Term> terms) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (final Term term : terms) {
            result = result.append(replace(term));
        }
        return result;
    }

    /**
     * Replaces in an ImmutableArray<QuantifiableVariable>.
     *
     * @param vars the array in which to perform the replacement.
     * @return the list of transformed variables.
     */
    public ImmutableArray<QuantifiableVariable> replace(
            ImmutableArray<? extends QuantifiableVariable> vars) {
        QuantifiableVariable[] result = new QuantifiableVariable[vars.size()];
        boolean changed = false;
        for (int i = 0, n = vars.size(); i < n; i++) {
            QuantifiableVariable qv = vars.get(i);
            QuantifiableVariable newQv = (QuantifiableVariable) replace(qv);
            result[i++] = newQv;
            if (newQv != qv) {
                changed = true;
            }
        }
        return changed ? new ImmutableArray<>(result) : (ImmutableArray<QuantifiableVariable>) vars;
    }
}
