/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.strategy.quantifierHeuristics.TriggerUtils;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * Support for the heap theory and array reads.
 *
 * Forbids the index packaging {@code arr(...)} and reads of the implicit {@code $created}
 * field as triggers, derives from every accepted trigger a variant whose reads of the quantified
 * variables match over any heap, so that a read written for one heap in a quantified formula
 * matches the reads a proof produces over its many other heaps, and supplies the indices a formula
 * writes as candidate
 * instances for the index it reads.
 */
final class HeapArrayTheorySupport implements QuantifierTheorySupport {

    /**
     * The trigger for an array access is the read.
     *
     * Around an access, three terms could trigger, and the verdicts keep them apart. The
     * packaging {@code arr(...)} wraps the index expression into a Field; it discriminates
     * nothing of its own, so it is never a trigger. The index expression below it can be one:
     * only compound expressions reach a verdict, a bare variable is no candidate to begin
     * with, and a compound expression matches only terms of its own shape. The read above
     * determines the accessed array, which the index expression alone does not, so its verdict
     * keeps the search going up to the select.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param enclosing the term the candidate is an argument of, null at the top of a literal
     * @param services access to the heap theory operators
     * @return the verdict
     */
    @Override
    public CandidateVerdict verdictOn(JTerm candidate, JTerm enclosing, Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if (heapLDT.isSelectOp(candidate.op())
                && candidate.sub(2).op() == heapLDT.getCreated()) {
            // a created read holds of every allocated object alike, so it selects nothing
            return CandidateVerdict.FORBIDDEN;
        }
        if (candidate.op() == heapLDT.getArr()) {
            // arr only packs the index expression into a Field. With a bare index it matches
            // the packaging of every access on the sequent; with a compound index it adds
            // no information to its argument, which receives its own verdict below.
            return CandidateVerdict.FORBIDDEN;
        }
        if (enclosing != null && enclosing.op() == heapLDT.getArr()) {
            // a compound index expression is a trigger of its own, but only the read above
            // determines the accessed array, so the select must become a trigger too
            return CandidateVerdict.PREFER_ENCLOSING;
        }
        return CandidateVerdict.ACCEPTABLE;
    }

    /**
     * Provides the heap-generalized variant of an accepted trigger, see {@link #freeHeaps}, and
     * the inner reads of a multi-dimensional array access as triggers of their own.
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the heap theory operators and term construction
     * @param metavariableFactory supplies the metavariables that stand for the heaps
     * @return the generalized triggers, empty if the term contains no read
     */
    @Override
    public List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services,
            MetavariableFactory metavariableFactory) {
        final List<JTerm> variants = new ArrayList<>();
        final JTerm generalized =
            freeHeaps(term, false, clauseVariables, variants, services, metavariableFactory);
        if (generalized != term) {
            variants.add(generalized);
        }
        return variants;
    }

    /**
     * The array indices a store of the formula writes, as candidates for the index a quantified
     * read of the same object reads.
     *
     * For {@code select(... store(h, o, arr(c), v) ..., o, arr(j))} the written index {@code c}
     * is a candidate for the quantified {@code j}: instantiating with it collapses the select by
     * the select-over-store rules. {@code c} is ground, so no trigger contains it and matching
     * never produces it.
     *
     * @param subterm a subterm of the quantified formula's matrix
     * @param variable the quantified variable an instance is sought for
     * @param services access to the heap theory operators
     * @return the written indices, possibly empty
     */
    @Override
    public List<JTerm> provideInstances(JTerm subterm, QuantifiableVariable variable,
            Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        // isSelectOp tests the operator directly. Do not build getSelect(subterm.sort()): that
        // constructs a select of the subterm's sort, which fails for e.g. the Null sort.
        if (!heapLDT.isSelectOp(subterm.op())) {
            return List.of();
        }
        final JTerm field = subterm.sub(2);
        if (field.op() != heapLDT.getArr() || !field.freeVars().contains(variable)) {
            return List.of();
        }
        final List<JTerm> indices = new ArrayList<>();
        collectWrittenIndices(subterm.sub(0), subterm.sub(1), heapLDT, indices);
        return indices;
    }

    /** Collects every ground array index written on {@code obj}'s array fields in {@code heap}. */
    private void collectWrittenIndices(JTerm heap, JTerm obj, HeapLDT heapLDT,
            List<JTerm> indices) {
        if (heap.sort() != heapLDT.targetSort()) {
            return;
        }
        if (heap.op() == heapLDT.getStore()) {
            final JTerm field = heap.sub(2);
            if (heap.sub(1).equals(obj) && field.op() == heapLDT.getArr()
                    && field.freeVars().isEmpty()) {
                indices.add(field.sub(0));
            }
        }
        for (int i = 0; i < heap.arity(); i++) {
            collectWrittenIndices(heap.sub(i), obj, heapLDT, indices);
        }
    }

    /**
     * Rebuilds a term with the heap of every read that carries a clause variable replaced by a
     * fresh metavariable.
     *
     * Such a read binds the variable to what stands at the variable's position in a read of the
     * same location, and the heap the location is read over does not discriminate: after a
     * method call or a loop the location is read over an anonymized heap, after an assignment
     * over a store, and the quantified formula names one of them. A read whose heap is a
     * metavariable matches the read over any heap. Every such read gets a metavariable of its
     * own, so the reads of one trigger match over different heaps.
     *
     * A read without a clause variable keeps its heap. It is part of the value the trigger
     * names, and a freed heap would only widen the match to values over other heaps: a guard
     * {@code x < p + result[1]} would then match sums with any read of {@code result[1]},
     * binding {@code x} to terms that prove nothing. A read whose heap contains a quantified
     * variable is left as it is.
     *
     * An array read is rebuilt with the component sort of its array. A formula may read
     * {@code x[i][i_1]} with sorts of its own choice (a nonNull specification types the final
     * read as plain Object), while the ground reads of a sequent carry the component sorts of
     * {@code x}'s array type, and parametric selects of different sorts are different
     * functions. The inner read of {@code x[i][i_1]} is added to {@code innerReads} if it
     * carries a clause variable: it is a trigger of its own and enters the multi-trigger pool
     * where it binds only part of the clause's variables.
     *
     * @param term the term to rebuild
     * @param arrayOfRead whether the term is the array argument of an enclosing array read
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param innerReads receives the rebuilt array reads that are the array of an enclosing read
     * @param services access to the heap theory operators and term construction
     * @param metavariableFactory supplies the metavariables that stand for the heaps
     * @return the rebuilt term, or {@code term} itself if it contains no read to free
     */
    private JTerm freeHeaps(JTerm term, boolean arrayOfRead,
            ImmutableSet<QuantifiableVariable> clauseVariables, List<JTerm> innerReads,
            Services services, MetavariableFactory metavariableFactory) {
        if (TriggerUtils.intersect(term.freeVars(), clauseVariables).isEmpty()) {
            return term;
        }
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        if (heapLDT.isSelectOp(term.op()) && term.sub(0).freeVars().isEmpty()) {
            final JTerm field = freeHeaps(term.sub(2), false, clauseVariables, innerReads,
                services, metavariableFactory);
            final boolean arrayRead = field.op() == heapLDT.getArr();
            final JTerm object = freeHeaps(term.sub(1), arrayRead, clauseVariables, innerReads,
                services, metavariableFactory);
            final JTerm heap = tb.var(metavariableFactory.fresh(heapLDT.targetSort()));
            final JTerm read = arrayRead && object.sort() instanceof ArraySort arraySort
                    ? tb.select(arraySort.elementSort(), heap, object, field)
                    : services.getTermFactory().createTerm(term.op(), heap, object, field);
            if (arrayOfRead && arrayRead
                    && !TriggerUtils.intersect(read.freeVars(), clauseVariables).isEmpty()) {
                innerReads.add(read);
            }
            return read;
        }
        JTerm[] subs = null;
        for (int i = 0; i < term.arity(); i++) {
            final JTerm sub = freeHeaps(term.sub(i), false, clauseVariables, innerReads,
                services, metavariableFactory);
            if (sub != term.sub(i)) {
                if (subs == null) {
                    subs = new JTerm[term.arity()];
                    for (int j = 0; j < term.arity(); j++) {
                        subs[j] = term.sub(j);
                    }
                }
                subs[i] = sub;
            }
        }
        if (subs == null) {
            return term;
        }
        return services.getTermFactory().createTerm(term.op(), new ImmutableArray<>(subs),
            term.boundVars(), null);
    }
}
