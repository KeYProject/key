/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


/**
 * Replaces operators in a term by other operators with the same signature, or subterms of the term
 * by other terms with the same sort. Does not replace in java blocks.
 */
public class OpReplacer {

    /**
     * Term factory.
     */
    private final TermFactory tf;

    /**
     * The replacement map.
     */
    private final ReplacementMap<? extends SVSubstitute, ? extends SVSubstitute> map;

    /**
     * <p>
     * Creates an {@code OpReplacer}.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link #OpReplacer(Map, TermFactory, Proof)} as it correctly deals with
     * {@link OriginTermLabels} and other proof-dependent features.
     * </p>
     *
     * @param map map mapping from the operators/terms to be replaced to the ones to replace them
     *        with
     * @param tf a term factory.
     */
    public OpReplacer(Map<? extends SVSubstitute, ? extends SVSubstitute> map, TermFactory tf) {
        this(map, tf, null);
    }

    /**
     * Creates an {@code OpReplacer}.
     *
     * @param map map mapping from the operators/terms to be replaced to the ones to replace them
     *        with.
     * @param tf a term factory.
     * @param proof the currently loaded proof
     */
    public OpReplacer(Map<? extends SVSubstitute, ? extends SVSubstitute> map, TermFactory tf,
            Proof proof) {
        assert map != null;

        this.map = map instanceof ReplacementMap
                ? (ReplacementMap<? extends SVSubstitute, ? extends SVSubstitute>) map
                : ReplacementMap.create(tf, proof, map);

        this.tf = tf;
    }

    /**
     * <p>
     * Replace a sub-term.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link OpReplacer#replace(Operator, Operator, Term, TermFactory, Proof)} as it correctly
     * deals with {@link OriginTermLabels} and other proof-dependent features.
     * </p>
     *
     * @param toReplace the sub-term to replace.
     * @param with the replacement sub-term.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the sub-term replaced.
     */
    public static Term replace(Term toReplace, Term with, Term in, TermFactory tf) {
        return replace(toReplace, with, in, tf, null);
    }

    /**
     * <p>
     * Replace a sub-term.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link OpReplacer#replace(Term, Term, ImmutableList, TermFactory, Proof)} as it correctly
     * deals with {@link OriginTermLabels} and other proof-dependent features.
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
        return replace(toReplace, with, in, tf, null);
    }

    /**
     * <p>
     * Replace an operator.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link OpReplacer#replace(Operator, Operator, Term, TermFactory, Proof)} as it correctly
     * deals with {@link OriginTermLabels} and other proof-dependent features.
     * </p>
     *
     * @param toReplace the operator to replace.
     * @param with the replacement operator.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the operator replaced.
     */
    public static Term replace(Operator toReplace, Operator with, Term in, TermFactory tf) {
        return replace(toReplace, with, in, tf, null);
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
     * @param proof the currently loaded proof.
     * @return a term with all occurences of the sub-term replaced.
     */
    public static Term replace(Term toReplace, Term with, Term in, TermFactory tf, Proof proof) {
        Map<Term, Term> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf, proof);
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
     * @param proof the currently loaded proof.
     * @return the terms with all occurences of the sub-term replaced.
     */
    public static ImmutableList<Term> replace(Term toReplace, Term with, ImmutableList<Term> in,
            TermFactory tf, Proof proof) {
        Map<Term, Term> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf, proof);
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
     * @param proof the currently loaded proof.
     * @return a term with all occurences of the operator replaced.
     */
    public static Term replace(Operator toReplace, Operator with, Term in, TermFactory tf,
            Proof proof) {
        Map<Operator, Operator> map = new LinkedHashMap<>();
        map.put(toReplace, with);
        OpReplacer or = new OpReplacer(map, tf, proof);
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

        for (SVSubstitute svs : map.keySet()) {
            if (term.equalsModTermLabels(svs)) {
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
                tf.createTerm(newOp, newSubTerms, newBoundVars, term.javaBlock(), term.getLabels());
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
     * Replaces in a list of triples of lists of terms.
     *
     * @param terms the terms in which to perform the replacement.
     * @return the list of transformed terms.
     */
    public ImmutableList<InfFlowSpec> replaceInfFlowSpec(ImmutableList<InfFlowSpec> terms) {
        ImmutableList<InfFlowSpec> result = ImmutableSLList.nil();
        if (terms == null) {
            return result;
        }

        for (final InfFlowSpec infFlowSpec : terms) {
            final ImmutableList<Term> preExpressions = replace(infFlowSpec.preExpressions);
            final ImmutableList<Term> postExpressions = replace(infFlowSpec.postExpressions);
            final ImmutableList<Term> newObjects = replace(infFlowSpec.newObjects);
            result = result.append(new InfFlowSpec(preExpressions, postExpressions, newObjects));
        }
        return result;
    }


    /**
     * Replaces in a set of terms.
     *
     * @param terms the terms in which to perform the replacement.
     * @return the set of transformed terms.
     */
    public ImmutableSet<Term> replace(ImmutableSet<Term> terms) {
        ImmutableSet<Term> result = DefaultImmutableSet.nil();
        for (final Term term : terms) {
            result = result.add(replace(term));
        }
        return result;
    }


    /**
     * Replaces in a map from Operator to Term.
     *
     * @param myMap the map in which to perform the replacement.
     * @return the transformed map.
     */
    public Map<Operator, Term> replace(Map<Operator, Term> myMap) {

        Map<Operator, Term> result = new LinkedHashMap<>();

        for (Map.Entry<Operator, Term> entry : myMap.entrySet()) {
            result.put(replace(entry.getKey()), replace(entry.getValue()));
        }
        return result;
    }


    /**
     * Replaces in an ImmutableArray<QuantifiableVariable>.
     *
     * @param vars the array in which to perform the replacement.
     * @return the list of transformed variables.
     */
    public ImmutableArray<QuantifiableVariable> replace(ImmutableArray<QuantifiableVariable> vars) {
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
        return changed ? new ImmutableArray<>(result) : vars;
    }
}
