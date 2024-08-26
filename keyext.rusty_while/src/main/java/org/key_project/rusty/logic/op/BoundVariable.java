/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import java.util.Objects;

import org.key_project.logic.Name;
import org.key_project.logic.ParsableVariable;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.op.Modifier;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.EqualsModProofIrrelevancy;

import org.jspecify.annotations.NonNull;

/**
 * The definition of logical variables.
 */
public final class BoundVariable extends AbstractSortedOperator
        implements QuantifiableVariable, ParsableVariable, EqualsModProofIrrelevancy {
    public BoundVariable(Name name, Sort sort) {
        super(name, sort, Modifier.RIGID);
    }

    @Override
    public boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof BoundVariable bv))
            return false;
        return name().equals(bv.name()) && sort().equals(bv.sort());
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
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Bound variable " + name() + " does not have children");
    }
}
