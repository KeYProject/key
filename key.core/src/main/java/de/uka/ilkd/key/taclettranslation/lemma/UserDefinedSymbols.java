/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.*;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.collection.ImmutableSet;

public class UserDefinedSymbols {
    static class NamedComparator implements Comparator<Named> {
        static final NamedComparator INSTANCE = new NamedComparator();

        @Override
        public int compare(Named o1, Named o2) {
            return o1.name().compareTo(o2.name());
        }
    }

    final UserDefinedSymbols parent;
    final Set<Function> usedExtraFunctions = new TreeSet<>(NamedComparator.INSTANCE);
    final Set<Function> usedExtraPredicates = new TreeSet<>(NamedComparator.INSTANCE);
    final Set<Sort> usedExtraSorts = new TreeSet<>(NamedComparator.INSTANCE);
    final Set<QuantifiableVariable> usedExtraVariables =
        new TreeSet<>(NamedComparator.INSTANCE);
    final Set<Named> usedSchemaVariables = new TreeSet<>(NamedComparator.INSTANCE);
    final ImmutableSet<Taclet> axioms;
    private final NamespaceSet referenceNamespaces;


    public UserDefinedSymbols(NamespaceSet referenceNamespaces, ImmutableSet<Taclet> axioms) {
        super();
        this.referenceNamespaces = referenceNamespaces;
        this.parent = null;
        this.axioms = axioms;

    }

    public UserDefinedSymbols(UserDefinedSymbols parent) {
        this.parent = parent;
        this.axioms = parent.axioms;
        this.referenceNamespaces = parent.referenceNamespaces;
    }

    private <T extends Named> void addUserDefiniedSymbol(T symbol, Set<T> set,
            Namespace<T> excludeNamespace) {
        if (!contains(symbol, set)) {
            if (symbol instanceof SchemaVariable
                    || excludeNamespace.lookup(symbol.name()) == null) {
                set.add(symbol);
            }
        }

    }

    private <T extends Named> boolean contains(T symbol, Set<T> set) {
        if (parent != null && parent.contains(symbol, set)) {
            return true;
        }

        return set.contains(symbol);
    }

    public void addFunction(Function symbol) {
        addUserDefiniedSymbol(symbol, usedExtraFunctions, referenceNamespaces.functions());
    }

    public void addPredicate(Function symbol) {
        addUserDefiniedSymbol(symbol, usedExtraPredicates, referenceNamespaces.functions());
    }

    public void addSort(Named symbol) {
        if (symbol != Sort.FORMULA) {
            Sort sort = (Sort) symbol;
            if (!(sort instanceof NullSort)) {
                for (Sort parentSort : sort.extendsSorts()) {
                    addSort(parentSort);
                }
            }
            addUserDefiniedSymbol(sort, usedExtraSorts, referenceNamespaces.sorts());
        }
    }

    public void addVariable(QuantifiableVariable symbol) {
        addUserDefiniedSymbol(symbol, usedExtraVariables, referenceNamespaces.variables());
    }

    public void addSchemaVariable(SchemaVariable symbol) {
        // FIXME: This breaks the generics of namespace
        addUserDefiniedSymbol(symbol, usedSchemaVariables,
            (Namespace) referenceNamespaces.variables());
    }

    public void addSymbolsToNamespaces(NamespaceSet namespaces) {
        addSymbolsToNamespace(namespaces.functions(), usedExtraFunctions);
        addSymbolsToNamespace(namespaces.functions(), usedExtraPredicates);
        addSymbolsToNamespace(namespaces.sorts(), usedExtraSorts);
        addSymbolsToNamespace(namespaces.variables(), usedExtraVariables);
    }

    private <T extends Named> void addSymbolsToNamespace(Namespace<T> namespace,
            Collection<T> symbols) {
        for (T symbol : symbols) {
            namespace.addSafely(symbol);
        }
    }

    public void replaceGenericByProxySorts() {
        Set<Sort> result = new HashSet<>();
        for (Sort sort : usedExtraSorts) {
            if (sort instanceof GenericSort) {
                GenericSort genSort = (GenericSort) sort;
                ProxySort proxySort = new ProxySort(genSort.name(), genSort.extendsSorts());
                result.add(proxySort);
            } else {
                result.add(sort);
            }
        }

        usedExtraSorts.clear();
        usedExtraSorts.addAll(result);
    }

    public String toString() {
        StringBuilder symbols = new StringBuilder("functions:\n");
        for (Named named : usedExtraFunctions) {
            symbols.append(named.name()).append(", ");
        }
        symbols.append("\npredicates:\n");
        for (Named named : usedExtraPredicates) {
            symbols.append(named.name()).append(", ");
        }
        symbols.append("\nsorts:\n");
        for (Named named : usedExtraSorts) {
            symbols.append(named.name()).append(", ");
        }
        symbols.append("\nschema variables:\n");
        for (Named named : usedSchemaVariables) {
            symbols.append(named.name()).append(", ");
        }
        symbols.append(parent != null ? "\n\n Parent: " + parent : "");
        return symbols.toString();
    }
}
