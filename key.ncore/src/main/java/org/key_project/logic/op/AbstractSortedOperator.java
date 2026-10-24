/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/// Abstract sorted operator class offering some common functionality.
public abstract class AbstractSortedOperator extends AbstractOperator
        implements SortedOperator {
    private final Sort sort;
    private final ImmutableList<Sort> argSorts;

    protected AbstractSortedOperator(Name name, ImmutableList<Sort> argSorts, Sort sort,
            @Nullable ImmutableList<Boolean> whereToBind, Modifier modifier) {
        super(name, argSorts.size(), whereToBind, modifier);
        this.argSorts = argSorts;
        this.sort = sort;
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Boolean[] whereToBind,
            Modifier modifier) {
        this(name, ImmutableList.of(argSorts), sort, ImmutableList.of(whereToBind),
            modifier);
    }

    protected AbstractSortedOperator(Name name, ImmutableList<Sort> argSorts, Sort sort,
            Modifier modifier) {
        this(name, argSorts, sort, null, modifier);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Modifier modifier) {
        this(name, ImmutableList.of(argSorts), sort, null, modifier);
    }

    protected AbstractSortedOperator(Name name, Sort sort, Modifier modifier) {
        this(name, ImmutableList.of(), sort, null, modifier);
    }

    @Override
    public final Sort sort(Sort[] sorts) {
        return sort;
    }

    @Override
    public final Sort argSort(int i) {
        return argSorts.get(i);
    }

    @Override
    public final ImmutableList<Sort> argSorts() {
        return argSorts;
    }

    @Override
    public final Sort sort() {
        return sort;
    }
}
