/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.WeakHashMap;

import org.key_project.logic.TerminalSyntaxElement;

/**
 * <p>
 * This class is a wrapper primarily used in logic operations where qualifiers, i.e., objects that
 * partly define a function but are not part of the syntax tree,
 * are referenced multiple times, such as in {@link ObserverFunction} and
 * {@link SortDependingFunction}. For example, for a function like {@code int::cast}, the
 * {@code int} sort is part of the function and should be considered when comparing it or traversing
 * the function.
 * </p>
 * <p>
 * But because sorts are not terms or operators, they are not part of a term's syntax tree.
 * This wrapper allows objects like sorts to appear in the syntax tree.
 * </p>
 * <p>
 * The class further ensures that two wrappers are referentially equal iff the wrapped objects are
 * equal.
 * </p>
 *
 * @param <T> The type of the qualifier object being wrapped.
 */
public class QualifierWrapper<T> implements TerminalSyntaxElement {
    private final T qualifier;

    private static final WeakHashMap<Object, QualifierWrapper<?>> INSTANCES = new WeakHashMap<>();

    private QualifierWrapper(T qualifier) {
        this.qualifier = qualifier;
    }

    /**
     * Get the instance for this qualifier. If none exist yet, create one.
     *
     * @param qualifier the qualifier for which we create an instance
     * @return new instance
     * @param <T> The type of the qualifier object being wrapped.
     */
    synchronized static <T> QualifierWrapper<T> get(T qualifier) {
        if (INSTANCES.containsKey(qualifier)) {
            return (QualifierWrapper<T>) INSTANCES.get(qualifier);
        }
        var q = new QualifierWrapper<>(qualifier);
        INSTANCES.put(qualifier, q);
        return q;
    }

    public T getQualifier() {
        return qualifier;
    }
}
