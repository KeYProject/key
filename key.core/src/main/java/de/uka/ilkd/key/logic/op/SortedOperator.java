package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;


/**
 * Operator with well-defined argument and result sorts.
 */
public interface SortedOperator extends Operator {

    Sort sort();

    Sort argSort(int i);

    ImmutableArray<Sort> argSorts();
}
