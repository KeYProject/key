package org.key_project.logic.op;

import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator with well-defined argument and result sorts.
 */
public interface SortedOperator {
    Sort sort();

    Sort argSort(int i);

    ImmutableArray<Sort> argSorts();
}
