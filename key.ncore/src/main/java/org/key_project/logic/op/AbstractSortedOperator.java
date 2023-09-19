package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Sorted;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public abstract class AbstractSortedOperator extends AbstractOperator implements SortedOperator, Sorted {
    private static final ImmutableArray<Sort> EMPTY_SORT_LIST = new ImmutableArray<>();
    private final Sort sort;
    private final ImmutableArray<Sort> argSorts;

    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
                                     ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, argSorts == null ? 0 : argSorts.size(), whereToBind, isRigid);
        if (sort == null) {
            throw new NullPointerException("Given sort is null");
        }
        this.argSorts = argSorts == null ? EMPTY_SORT_LIST : argSorts;
        this.sort = sort;
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Boolean[] whereToBind,
                                     boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort,
                new ImmutableArray<>(whereToBind), isRigid);
    }

    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort,
                                     boolean isRigid) {
        this(name, argSorts, sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, boolean isRigid) {
        this(name, new ImmutableArray<>(argSorts), sort, null, isRigid);
    }

    protected AbstractSortedOperator(Name name, Sort sort, boolean isRigid) {
        this(name, (ImmutableArray<Sort>) null, sort, null, isRigid);
    }

    @Override
    public final Sort sort(ImmutableArray<Term> terms) {
        return sort;
    }

    @Override
    public final Sort argSort(int i) {
        return argSorts.get(i);
    }

    @Override
    public final ImmutableArray<Sort> argSorts() {
        return argSorts;
    }

    @Override
    public final Sort sort() {
        return sort;
    }
}
