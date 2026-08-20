/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.strategy.quantifierHeuristics.TriggerUtils;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

/**
 * Support for the heap theory and array reads.
 *
 * Rejects the bare array-index constructor {@code arr(i)} (an index, not a read) and reads of
 * the implicit {@code $created} field, provides array-read triggers generalized over the heap
 * so that a read written for one heap in a quantified formula matches the reads a proof produces
 * over its many other heaps, and supplies the indices a formula writes as candidate instances
 * for the index it reads.
 */
final class HeapArrayTheorySupport implements QuantifierTheorySupport {

    /**
     * Rejects the bare array index {@code arr(i)} and reads of the implicit created field, both of
     * which flood the instantiation when matched on their own.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param services access to the heap theory operators
     * @return whether the candidate is rejected
     */
    @Override
    public boolean rejectsAsTrigger(JTerm candidate, Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        // we do not want to match on expressions a.$created
        if (heapLDT.isSelectOp(candidate.op()) && candidate.sub(2).op().name().toString()
                .endsWith(PipelineConstants.IMPLICIT_CREATED)) {
            return true;
        }
        // the array-index constructor arr(i) alone is an index, not a read: matching on it
        // instantiates with every index literal of any array on any heap. The enclosing select is
        // the meaningful trigger (see the generalized variants provided below).
        return candidate.op() == heapLDT.getArr();
    }

    /**
     * An array index gives way to the read around it: alone it matches every integer term on the
     * sequent, while the read says which access is meant. Both are registered, so no instantiation
     * is lost.
     */
    @Override
    public boolean prefersEnclosingTrigger(JTerm candidate, JTerm enclosing, Services services) {
        return enclosing != null
                && enclosing.op() == services.getTypeConverter().getHeapLDT().getArr();
    }

    /**
     * Provides the heap-generalized array read triggers, one per array dimension of the read.
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the heap theory operators and term construction
     * @return the generalized read triggers, possibly empty
     */
    @Override
    public List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services,
            MetavariableFactory metavariableFactory) {
        return dimensionVariants(term, clauseVariables, services, metavariableFactory);
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
     * The generalized triggers for an array read, one per array dimension it goes through. This
     * is the single generalization path: for a one-dimensional read it yields one trigger, for a
     * read through a multi-dimensional array one per level.
     *
     * Two things must be generalized. The heap, because after simplification the read occurs over
     * the many heaps of a proof (store chains of symbolic execution, an anonymized loop heap),
     * not only the one written in the formula; a fresh metavariable per level stands for any heap.
     * And the select sorts, because a formula may read {@code x[i][i_1]} with sorts of its own
     * choice (a nonNull specification types the final read as plain Object), while the ground reads
     * in a sequent are built with the component sorts of {@code x}'s array type, one per dimension.
     * A trigger carrying the formula's sorts never matches: parametric selects of different sorts
     * are different functions.
     *
     * For a select chain over an array-sorted base this method therefore rebuilds the access path
     * once per depth, with the component sort of the base's array type at that depth and a fresh
     * metavariable per level: for {@code x[i][i_1]} the triggers {@code select(H0, x, arr(i))}
     * and {@code select(H1, select(H0, x, arr(i)), arr(i_1))}, whose metavariables {@code H0} and
     * {@code H1} each stand for any heap, and each carrying the sorts a ground read of that depth
     * actually has. Prefixes that bind only part of the clause variables enter the multi-trigger
     * pool as usual.
     *
     * @param term an accepted array read trigger
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the heap theory operators and term construction
     * @return one generalized read trigger per array dimension, possibly empty
     */
    private List<JTerm> dimensionVariants(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services,
            MetavariableFactory metavariableFactory) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        final List<JTerm> variants = new ArrayList<>();
        // decompose the select chain: walk through the object position collecting the arr
        // array indices, innermost first
        final List<JTerm> arrayIndices = new ArrayList<>();
        JTerm base = term;
        while (heapLDT.isSelectOp(base.op()) && base.sub(2).op() == heapLDT.getArr()) {
            arrayIndices.add(0, base.sub(2).sub(0));
            base = base.sub(1);
        }
        if (arrayIndices.isEmpty() || !(base.sort() instanceof ArraySort)) {
            return variants;
        }
        boolean anyVar = false;
        for (final JTerm c : arrayIndices) {
            if (!TriggerUtils.intersect(c.freeVars(), clauseVariables).isEmpty()) {
                anyVar = true;
            }
        }
        if (!anyVar) {
            return variants;
        }
        // rebuild the path bottom-up with the array's component sorts
        Sort sort = base.sort();
        JTerm read = base;
        for (int depth = 0; depth < arrayIndices.size(); depth++) {
            if (!(sort instanceof ArraySort arraySort)) {
                break;
            }
            sort = arraySort.elementSort();
            final JTerm heapVar = tb.var(metavariableFactory.fresh(heapLDT.targetSort()));
            final JTerm arrField = tb.func(heapLDT.getArr(), arrayIndices.get(depth));
            read = tb.select(sort, heapVar, read, arrField);
            if (!TriggerUtils.intersect(read.freeVars(), clauseVariables).isEmpty()
                    && !read.equals(term)) {
                variants.add(read);
            }
        }
        return variants;
    }
}
