/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.ParsableVariable;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.util.EqualsModProofIrrelevancy;

import java.util.Objects;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable, EqualsModProofIrrelevancy {

    public LogicVariable(Name name, Sort sort) {
        super(name, sort, Modifier.RIGID);
        assert sort != RustyDLTheory.FORMULA;
        assert sort != RustyDLTheory.UPDATE;
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

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Logic variable " + name() + " does not have children");
    }
}
