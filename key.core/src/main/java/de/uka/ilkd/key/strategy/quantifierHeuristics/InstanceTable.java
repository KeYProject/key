/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;

import org.key_project.logic.Term;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * The candidate instances of one quantified formula on one sequent, each with its cost and its
 * origin.
 *
 * The table is what the strategy reads: the generator iterates {@link #instances()}, and the
 * cost feature, the approval check and the tie-break look instances up. A looked-up instance may
 * arrive wrapped in a cast, because the generator casts a candidate whose sort does not fit the
 * quantified variable; {@link #normalize} takes the wrapper off, in this one place.
 *
 * Instances equal up to term labels share one entry. Of several offers for one instance the
 * cheapest is kept.
 */
final class InstanceTable {

    /**
     * One recorded instance.
     *
     * @param cost the instance's predicted cost plus its origin's surcharge
     * @param origin why the instance is offered
     */
    record Entry(long cost, Origin origin) {
    }

    private final Map<Term, Entry> entries = new LinkedHashMap<>();

    /**
     * The recorded instances bucketed by {@link Term#nameHash()}. Two terms equal up to term
     * labels share that hash, so the label-insensitive duplicate check in {@link #record}
     * compares only within one bucket instead of scanning every recorded instance.
     */
    private final Map<Integer, List<Term>> byNameHash = new HashMap<>();

    /**
     * Records one offer for an instance. The first offer creates the entry; a later offer
     * replaces it unless it is more expensive.
     *
     * @param inst the instance
     * @param cost the instance's predicted cost plus its origin's surcharge
     * @param origin why the instance is offered
     */
    void record(Term inst, long cost, Origin origin) {
        Term key = inst;
        Entry old = entries.get(inst);
        if (old == null) {
            final List<Term> bucket = byNameHash.get(inst.nameHash());
            if (bucket != null) {
                for (final Term existing : bucket) {
                    if (((JTerm) existing).equalsModProperty(inst,
                        IRRELEVANT_TERM_LABELS_PROPERTY)) {
                        key = existing;
                        old = entries.get(existing);
                        break;
                    }
                }
            }
            if (old == null) {
                byNameHash.computeIfAbsent(inst.nameHash(), h -> new ArrayList<>(2)).add(inst);
            }
        }
        if (old == null || old.cost() >= cost) {
            entries.put(key, new Entry(cost, origin));
        }
    }

    /**
     * The entry of an instance, or null if the instance was never offered. The query is
     * normalized first, so a cast-wrapped candidate finds the entry of its argument.
     *
     * @param query the instance as the strategy holds it
     * @param services access to the cast symbol
     * @return the entry, or null
     */
    Entry entryOf(Term query, Services services) {
        final Entry entry = entries.get(query);
        if (entry != null) {
            return entry;
        }
        final Term normalized = normalize(query, services);
        return normalized == query ? null : entries.get(normalized);
    }

    /**
     * The instance as this table keys it: a candidate the generator wrapped in a cast is keyed
     * by the cast's argument.
     *
     * @param query the instance as the strategy holds it
     * @param services access to the cast symbol
     * @return the table's key for the instance
     */
    Term normalize(Term query, Services services) {
        if (query.op() instanceof ParametricFunctionInstance pfi
                && pfi.getBase() == services.getJavaDLTheory().getCastSymbol(services)) {
            return query.sub(0);
        }
        return query;
    }

    /** The recorded instances, in the order they were first offered. */
    Set<Term> instances() {
        return entries.keySet();
    }
}
