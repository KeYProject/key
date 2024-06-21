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
 * It uses De Brujin indices instead of names.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable, EqualsModProofIrrelevancy {

    private final int index ;

    public LogicVariable(int index, Sort sort) {
        super(new Name("@"+index), sort, Modifier.RIGID);
        assert sort != RustyDLTheory.FORMULA;
        assert sort != RustyDLTheory.UPDATE;
        this.index = index;
    }

    public int getIndex() {
        return index;
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
        return index == that.index;
    }

    @Override
    public int hashCodeModProofIrrelevancy() {
        // TODO
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
