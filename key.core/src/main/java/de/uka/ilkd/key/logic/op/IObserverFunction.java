/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

import org.key_project.util.collection.ImmutableArray;

public interface IObserverFunction extends SortedOperator {

    /**
     * Returns the result type of this symbol.
     */
    KeYJavaType getType();

    /**
     * Returns the container type of this symbol; for non-static observer symbols, this corresponds
     * to the sort of its second argument.
     */
    KeYJavaType getContainerType();

    /**
     * Tells whether the observer symbol is static.
     */
    boolean isStatic();

    /**
     * Check the state count of the declaration (no_state = 0, two_state = 2, 1 otherwise).
     */
    int getStateCount();

    /**
     * Check the heap count of the declaration, e.g. the base heap and extra heap.
     */
    int getHeapCount(Services services);

    /**
     * Gives the number of parameters of the observer symbol. "Parameters" here includes only the
     * *explicit* parameters, not the heap and the receiver object. Thus, for observer symbols
     * representing model fields, this will always return 0.
     */
    int getNumParams();

    /**
     * Gives the type of the i-th parameter of this observer symbol. "Parameters" here includes only
     * the *explicit* parameters, not the heap and the receiver object.
     */
    KeYJavaType getParamType(int i);

    /**
     * Returns the parameter types of this observer symbol. "Parameters" here includes only the
     * *explicit* parameters, not the heap and the receiver object.
     */
    ImmutableArray<KeYJavaType> getParamTypes();

}
