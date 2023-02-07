/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable {

    public LogicVariable(Name name, Sort sort) {
        super(name, sort, true);
        assert sort != Sort.FORMULA;
        assert sort != Sort.UPDATE;
    }


    @Override
    public String toString() {
        return name() + ":" + sort();
    }
}
