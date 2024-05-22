/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.WeakHashMap;

import org.key_project.logic.SyntaxElement;

public class Qualifier<T> implements SyntaxElement {
    private final T qualifier;

    private static final WeakHashMap<Object, Qualifier<?>> INSTANCES = new WeakHashMap<>();

    private Qualifier(T qualifier) {
        this.qualifier = qualifier;
    }

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

    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
