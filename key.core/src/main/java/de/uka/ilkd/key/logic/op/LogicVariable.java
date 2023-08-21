/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.Objects;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.EqualsModProofIrrelevancy;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable, EqualsModProofIrrelevancy {

    public LogicVariable(Name name, Sort sort) {
        super(name, sort, true);
        assert sort != Sort.FORMULA;
        assert sort != Sort.UPDATE;
    }


    @Override
    public String toString() {
        return name() + ":" + sort();
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof LogicVariable)) {
            return false;
        }
        LogicVariable that = (LogicVariable) obj;
        return name().equals(that.name()) && sort().equals(that.sort());
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        return Objects.hash(name(), sort());
    }
}
