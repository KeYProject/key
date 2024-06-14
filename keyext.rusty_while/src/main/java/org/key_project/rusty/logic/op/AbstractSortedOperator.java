package org.key_project.rusty.logic.op;

import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

public abstract class AbstractSortedOperator extends org.key_project.logic.op.AbstractSortedOperator {
    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort, @Nullable ImmutableArray<Boolean> whereToBind, Modifier modifier) {
        super(name, argSorts, sort, whereToBind, modifier);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Boolean[] whereToBind, Modifier modifier) {
        super(name, argSorts, sort, whereToBind, modifier);
    }

    protected AbstractSortedOperator(Name name, ImmutableArray<Sort> argSorts, Sort sort, Modifier modifier) {
        super(name, argSorts, sort, modifier);
    }

    protected AbstractSortedOperator(Name name, Sort[] argSorts, Sort sort, Modifier modifier) {
        super(name, argSorts, sort, modifier);
    }

    protected AbstractSortedOperator(Name name, Sort sort, Modifier modifier) {
        super(name, sort, modifier);
    }
}
