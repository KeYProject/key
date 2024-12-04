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

import org.jspecify.annotations.NonNull;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 * It uses De Brujin indices instead of names.
 * <br>
 * This class is for occurrences of logic variables in formulas/terms. For the class
 * for definition of logical variables {@see BoundVariable}.
 */
public final class LogicVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable {

    private final int index;

    public LogicVariable(int index, Sort sort) {
        super(new Name("@" + index), sort, Modifier.RIGID);
        assert sort != RustyDLTheory.FORMULA;
        assert sort != RustyDLTheory.UPDATE;
        this.index = index;
    }

    public int getIndex() {
        return index;
    }

    @Override
    public @NonNull String toString() {
        return name() + ":" + sort();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Logic variable " + name() + " does not have children");
    }
}
