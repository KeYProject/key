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

import org.jspecify.annotations.NonNull;

/**
 * The definition of logical variables.
 */
public final class BoundVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable {
    public BoundVariable(Name name, Sort sort) {
        super(name, sort, Modifier.RIGID);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Bound variable " + name() + " does not have children");
    }
}
