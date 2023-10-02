/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public abstract class AbstractSortedOperator<S extends Sort<S>, T extends Term> extends AbstractOperator<S, T>
        implements SortedOperator<S, T> {
    private static final ImmutableArray EMPTY_SORT_LIST = new ImmutableArray<>();
    private static <S extends Sort<S>> ImmutableArray<S> getEmptySortList() {
        return (ImmutableArray<S>) EMPTY_SORT_LIST;
    }
    private final S sort;
    private final ImmutableArray<S> argSorts;

    protected AbstractSortedOperator(Name name, ImmutableArray<S> argSorts, S sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, argSorts == null ? 0 : argSorts.size(), whereToBind, isRigid);
        if (sort == null) {
            throw new NullPointerException("Given sort is null");
        }
        this.argSorts = argSorts == null ? getEmptySortList() : argSorts;
        this.sort = sort;
    }

    protected AbstractSortedOperator(Name name, Object[] argSorts, S sort, Boolean[] whereToBind,
            boolean isRigid) {
        this(name, new ImmutableArray<>((S[]) argSorts), sort,
            new ImmutableArray<>(whereToBind), isRigid);
    }

    protected AbstractSortedOperator(Name name, ImmutableArray<S> argSorts, S sort,
            boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Object[] argSorts, S sort, boolean isRigid) {
        this(name, new ImmutableArray<>((S[]) argSorts), sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, S sort, boolean isRigid) {
        this(name, (ImmutableArray<S>) null, sort, null, isRigid);
    }



    @Override
    public final S sort(S[] sorts) {
        return sort;
    }

    @Override
    public final S argSort(int i) {
        return argSorts.get(i);
    }

    @Override
    public final ImmutableArray<S> argSorts() {
        return argSorts;
    }

    @Override
    public final S sort() {
        return sort;
    }
}
