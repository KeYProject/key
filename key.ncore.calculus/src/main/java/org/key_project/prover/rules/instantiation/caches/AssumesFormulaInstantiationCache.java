/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.rules.instantiation.caches;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;

/// A simple cache for the results of the method `createList`.
///
/// Implemented as two small direct-mapped tables indexed by the identity hash of the
/// semisequent. Entries are immutable [Pair]s with final fields, so the table can be
/// read and written without locking: a racy read at worst observes an older entry,
/// which only causes a cache miss. (The previous implementation used access-ordered
/// LRU maps whose `get` mutates the map, guarded only by a read lock.)
public final class AssumesFormulaInstantiationCache {

    private static final int SIZE = 64; // power of two

    // The cached type is bound to the deprecated ImmutableArray through
    // AssumesFormulaInstSeq.createList. Generic array creation is not possible, so the arrays
    // stay raw (rawtypes) and the element-store conversion needs the unchecked suppression.
    @SuppressWarnings({ "unchecked", "rawtypes", "deprecation" })
    private final Pair<Semisequent, ImmutableArray<AssumesFormulaInstantiation>>[] antecCache =
        new Pair[SIZE];
    @SuppressWarnings({ "unchecked", "rawtypes", "deprecation" })
    private final Pair<Semisequent, ImmutableArray<AssumesFormulaInstantiation>>[] succCache =
        new Pair[SIZE];

    private static int indexFor(Semisequent s) {
        return System.identityHashCode(s) & (SIZE - 1);
    }

    // ImmutableArray is deprecated in favor of ImmutableList; the cached value type is dictated
    // by AssumesFormulaInstSeq.createList.
    @SuppressWarnings("deprecation")
    public @Nullable ImmutableArray<AssumesFormulaInstantiation> get(boolean antec, Semisequent s) {
        final Pair<Semisequent, ImmutableArray<AssumesFormulaInstantiation>> p =
            (antec ? antecCache : succCache)[indexFor(s)];
        return p != null && p.first == s ? p.second : null;
    }

    // ImmutableArray is deprecated in favor of ImmutableList; the cached value type is dictated
    // by AssumesFormulaInstSeq.createList.
    @SuppressWarnings("deprecation")
    public void put(boolean antec, Semisequent s,
            ImmutableArray<AssumesFormulaInstantiation> value) {
        (antec ? antecCache : succCache)[indexFor(s)] = new Pair<>(s, value);
    }
}
