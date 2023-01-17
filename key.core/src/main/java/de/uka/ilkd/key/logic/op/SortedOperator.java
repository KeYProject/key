package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Operator with well-defined argument and result sorts.
 */
public interface SortedOperator extends Operator {

    Sort sort();

    Sort argSort(int i);

    public ImmutableArray<Sort> argSorts();
}
