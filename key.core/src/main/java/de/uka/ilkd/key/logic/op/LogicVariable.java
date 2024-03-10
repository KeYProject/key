/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import java.util.Objects;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.EqualsModProofIrrelevancy;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable, EqualsModProofIrrelevancy {

    public LogicVariable(Name name, Sort sort) {
        super(name, sort, true);
        assert sort != JavaDLTheory.FORMULA;
        assert sort != JavaDLTheory.UPDATE;
    }


    @Override
    public String toString() {
        return name() + ":" + sort();
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof LogicVariable that)) {
            return false;
        }
        return name().equals(that.name()) && sort().equals(that.sort());
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        return Objects.hash(name(), sort());
    }
}
