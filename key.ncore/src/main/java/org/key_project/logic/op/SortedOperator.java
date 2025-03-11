/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Sorted;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator with well-defined argument and result sorts.
 */
public interface SortedOperator extends Operator, Sorted {
    Sort argSort(int i);

    ImmutableArray<Sort> argSorts();
}
