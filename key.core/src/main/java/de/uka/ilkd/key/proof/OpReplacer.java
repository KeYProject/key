/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.util.InfFlowSpec;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;


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
    private final ReplacementMap<? extends SyntaxElement, ? extends SyntaxElement> map;

    /**
     * <p>
     * Creates an {@code OpReplacer}.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link #OpReplacer(Map, TermFactory, Proof)} as it correctly deals with
     * {@link de.uka.ilkd.key.logic.label.OriginTermLabel}s and other proof-dependent features.
     * </p>
     *
     * @param map map mapping from the operators/terms to be replaced to the ones to replace them
     *        with
     * @param tf a term factory.
     */
    public OpReplacer(Map<? extends SyntaxElement, ? extends SyntaxElement> map, TermFactory tf) {
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
    public OpReplacer(Map<? extends SyntaxElement, ? extends SyntaxElement> map, TermFactory tf,
            Proof proof) {
        assert map != null;

        this.map = map instanceof ReplacementMap
                ? (ReplacementMap<? extends SyntaxElement, ? extends SyntaxElement>) map
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
     * {@link OpReplacer#replace(Operator, Operator, JTerm, TermFactory, Proof)} as it correctly
     * deals with {@link de.uka.ilkd.key.logic.label.OriginTermLabel}s and other proof-dependent
     * features.
     * </p>
     *
     * @param toReplace the sub-term to replace.
     * @param with the replacement sub-term.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the sub-term replaced.
     */
    public static JTerm replace(JTerm toReplace, JTerm with, JTerm in, TermFactory tf) {
        return replace(toReplace, with, in, tf, null);
    }

    /**
     * <p>
     * Replace a sub-term.
     * </p>
     *
     * <p>
     * If there is a proof currently loaded, you may want to use
     * {@link OpReplacer#replace(JTerm, JTerm, ImmutableList, TermFactory, Proof)} as it correctly
     * deals with {@link de.uka.ilkd.key.logic.label.OriginTermLabel}s and other proof-dependent
     * features.
     * </p>
     *
     * @param toReplace the sub-term to replace.
     * @param with the replacement sub-term.
     * @param in the terms in which to perform the replacement.
     * @param tf a term factory.
     * @return the terms with all occurences of the sub-term replaced.
     */
    public static ImmutableList<JTerm> replace(JTerm toReplace, JTerm with, ImmutableList<JTerm> in,
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
     * {@link OpReplacer#replace(Operator, Operator, JTerm, TermFactory, Proof)} as it correctly
     * deals with {@link de.uka.ilkd.key.logic.label.OriginTermLabel}s and other proof-dependent
     * features.
     * </p>
     *
     * @param toReplace the operator to replace.
     * @param with the replacement operator.
     * @param in the term in which to perform the replacement.
     * @param tf a term factory.
     * @return a term with all occurences of the operator replaced.
     */
    public static JTerm replace(Operator toReplace, Operator with, JTerm in, TermFactory tf) {
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
    public static JTerm replace(JTerm toReplace, JTerm with, JTerm in, TermFactory tf,
            Proof proof) {
        Map<JTerm, JTerm> map = new LinkedHashMap<>();
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
    public static ImmutableList<JTerm> replace(JTerm toReplace, JTerm with, ImmutableList<JTerm> in,
            TermFactory tf, Proof proof) {
        Map<JTerm, JTerm> map = new LinkedHashMap<>();
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
    public static JTerm replace(Operator toReplace, Operator with, JTerm in, TermFactory tf,
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
    public JTerm replace(JTerm term) {
        if (term == null) {
            return null;
        }
        final JTerm newTerm = (JTerm) map.get(term);
        if (newTerm != null) {
            return newTerm;
        }

        for (SyntaxElement svs : map.keySet()) {
            if (svs instanceof JTerm t && TERM_LABELS_PROPERTY.equalsModThisProperty(term, t)) {
                return (JTerm) map.get(svs);
            }
        }

        final Operator newOp = replace(term.op());

        final int arity = term.arity();
        final JTerm[] newSubTerms = new JTerm[arity];
        boolean changedSubTerm = false;
        for (int i = 0; i < arity; i++) {
            JTerm subTerm = term.sub(i);
            newSubTerms[i] = replace(subTerm);

            if (newSubTerms[i] != subTerm) {
                changedSubTerm = true;
            }
        }
        final ImmutableArray<QuantifiableVariable> newBoundVars = replace(term.boundVars());

        final JTerm result;
        if (newOp != term.op() || changedSubTerm || newBoundVars != term.boundVars()) {
            result =
                tf.createTerm(newOp, newSubTerms, newBoundVars,
                    term.getLabels());
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
    public ImmutableList<JTerm> replace(ImmutableList<JTerm> terms) {
        ImmutableList<JTerm> result = ImmutableSLList.nil();
        for (final JTerm term : terms) {
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
            final ImmutableList<JTerm> preExpressions = replace(infFlowSpec.preExpressions);
            final ImmutableList<JTerm> postExpressions = replace(infFlowSpec.postExpressions);
            final ImmutableList<JTerm> newObjects = replace(infFlowSpec.newObjects);
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
    public ImmutableSet<JTerm> replace(ImmutableSet<JTerm> terms) {
        ImmutableSet<JTerm> result = DefaultImmutableSet.nil();
        for (final JTerm term : terms) {
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
    public Map<Operator, JTerm> replace(Map<Operator, JTerm> myMap) {

        Map<Operator, JTerm> result = new LinkedHashMap<>();

        for (Map.Entry<Operator, JTerm> entry : myMap.entrySet()) {
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
    public ImmutableArray<QuantifiableVariable> replace(
            ImmutableArray<QuantifiableVariable> vars) {
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
