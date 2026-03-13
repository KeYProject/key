/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.collection.Pair;

import org.jspecify.annotations.Nullable;

class ContractClauses {
    public @Nullable JTerm measuredBy;
    public @Nullable JTerm decreases;
    public @Nullable JTerm signals;
    public @Nullable JTerm signalsOnly;
    public @Nullable JTerm diverges;
    public @Nullable JTerm returns;

    static final Clauses<Label, JTerm> BREAKS = new Clauses<>();
    static final Clauses<Label, JTerm> CONTINUES = new Clauses<>();

    /**
     * The name 'assignable' is kept here for legacy reasons.
     * Note that KeY does only verify what can be modified (i.e., what is 'modifiable').
     */
    static final Clauses<LocationVariable, JTerm> ASSIGNABLE = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> ACCESSIBLE = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> ENSURES = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> ENSURES_FREE = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> REQUIRES = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> REQUIRES_FREE = new Clauses<>();
    static final Clauses<LocationVariable, JTerm> AXIOMS = new Clauses<>();
    static final Clauses<LocationVariable, Boolean> HAS_MODS = new Clauses<>();


    @SuppressWarnings("unused")
    static class Clauses<K, V> {
    }

    private final Map<Clauses<?, ?>, List<Pair<Object, Object>>> clauseData = new LinkedHashMap<>();

    public <K, V> ContractClauses add(Clauses<K, V> type, K heapOrLabel, V t) {
        List<Pair<Object, Object>> list =
            clauseData.computeIfAbsent(type, key -> new LinkedList<>());
        list.add(new Pair<>(heapOrLabel, t));
        return this;
    }

    @SuppressWarnings("unchecked")
    public <K, V> List<Pair<K, V>> get(Clauses<K, V> type) {
        List<Pair<Object, Object>> list =
            clauseData.computeIfAbsent(type, key -> new LinkedList<>());
        return list.stream().map(p -> new Pair<>((K) p.first, (V) p.second))
                .collect(Collectors.toList());
    }
}
