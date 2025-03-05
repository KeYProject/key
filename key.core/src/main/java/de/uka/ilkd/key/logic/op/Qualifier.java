/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.WeakHashMap;

import org.key_project.logic.TerminalSyntaxElement;

/**
 * This class is primarily used in logic operations where qualifiers (e.g., types or sorts)
 * are referenced multiple times, such as in {@link ObserverFunction} and
 * {@link SortDependingFunction}.
 * It helps to ensure that qualifiers maintain identity-based equality when reused.
 * <p>
 * As a qualifier is part of the structure of a symbol, e.g., function symbols, it has to be its own
 * AST node. Hence, it is part of the structure reached by navigating through
 * {@link org.key_project.logic.SyntaxElement} and
 * {@link org.key_project.logic.SyntaxElementCursor}.
 * </p>
 *
 * @param <T> The type of the qualifier object being wrapped.
 */
public class Qualifier<T> implements TerminalSyntaxElement {
    private final T qualifier;

    private static final WeakHashMap<Object, Qualifier<?>> INSTANCES = new WeakHashMap<>();

    private Qualifier(T qualifier) {
        this.qualifier = qualifier;
    }

    /**
     * Get the instance for this qualifier. If none exist yet, create one.
     *
     * @param qualifier the qualifier for which we create an instance
     * @return new instance
     * @param <T> The type of the qualifier object being wrapped.
     */
    synchronized static <T> Qualifier<T> create(T qualifier) {
        if (INSTANCES.containsKey(qualifier)) {
            return (Qualifier<T>) INSTANCES.get(qualifier);
        }
        var q = new Qualifier<>(qualifier);
        INSTANCES.put(qualifier, q);
        return q;
    }

    public T getQualifier() {
        return qualifier;
    }
}
