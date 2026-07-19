/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.ArraySort;

import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

/**
 * Support for the heap theory and array reads.
 *
 * Rejects the bare array-index constructor {@code arr(i)} (a coordinate, not a read) and reads of
 * the implicit {@code $created} field, and provides array-read triggers generalized over the heap
 * so that a read written for one heap in a quantified formula matches the reads a proof produces
 * over its many other heaps.
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
        // the array-index constructor arr(i) alone is a coordinate, not a read: matching on it
        // instantiates with every index literal of any array on any heap. The enclosing select is
        // the meaningful trigger (see the generalized variants provided below).
        return candidate.op() == heapLDT.getArr();
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
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services) {
        return dimensionVariants(term, clauseVariables, services);
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
     * heap wildcard per level: for {@code x[i][i_1]} the triggers {@code x[i]} and
     * {@code x[i][i_1]}, each carrying the sorts a ground read of that depth actually has. Prefixes
     * that bind only part of the clause variables enter the multi-trigger pool as usual.
     *
     * @param term an accepted array read trigger
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the heap theory operators and term construction
     * @return one generalized read trigger per array dimension, possibly empty
     */
    private List<JTerm> dimensionVariants(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        final List<JTerm> variants = new ArrayList<>();
        // decompose the select chain: walk through the object position collecting the arr
        // coordinates, innermost first
        final List<JTerm> coordinates = new ArrayList<>();
        JTerm base = term;
        while (heapLDT.isSelectOp(base.op()) && base.sub(2).op() == heapLDT.getArr()) {
            coordinates.add(0, base.sub(2).sub(0));
            base = base.sub(1);
        }
        if (coordinates.isEmpty() || !(base.sort() instanceof ArraySort)) {
            return variants;
        }
        boolean anyVar = false;
        for (final JTerm c : coordinates) {
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
        for (int depth = 0; depth < coordinates.size(); depth++) {
            if (!(sort instanceof ArraySort arraySort)) {
                break;
            }
            sort = arraySort.elementSort();
            final JTerm heapVar =
                tb.var(heapWildcard(term, clauseVariables, heapLDT.targetSort(), "_d" + depth));
            final JTerm arrField = tb.func(heapLDT.getArr(), coordinates.get(depth));
            read = tb.select(sort, heapVar, read, arrField);
            if (!TriggerUtils.intersect(read.freeVars(), clauseVariables).isEmpty()
                    && !read.equals(term)) {
                variants.add(read);
            }
        }
        return variants;
    }

    /**
     * A fresh heap-sorted metavariable standing for "any heap" in a generalized trigger. Its name
     * is derived from the quantified variables of the read (plus a caller-chosen suffix to keep
     * several wildcards of one trigger apart) rather than from creation order, so that the
     * metavariable ordering (and through it the unification result and the chosen instances) does
     * not depend on which goal builds its trigger set first.
     *
     * @param select the read the wildcard is built for
     * @param clauseVariables the quantified variables of the clause the read belongs to
     * @param heapSort the sort of heaps
     * @param suffix keeps several wildcards of one trigger apart
     * @return a fresh heap-sorted metavariable
     */
    private static Metavariable heapWildcard(JTerm select,
            ImmutableSet<QuantifiableVariable> clauseVariables, Sort heapSort, String suffix) {
        final StringBuilder name = new StringBuilder("heapWildcard");
        for (final QuantifiableVariable v : TriggerUtils.intersect(select.freeVars(),
            clauseVariables)) {
            name.append('_').append(v.name());
        }
        name.append(suffix);
        return new Metavariable(new Name(name.toString()), heapSort);
    }
}
