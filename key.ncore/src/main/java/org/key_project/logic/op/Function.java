/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Objects of this class represent function and predicate symbols. Note that program variables are a
 * separate syntactic category, and not a type of function.
 */
public abstract class Function extends org.key_project.logic.op.AbstractSortedOperator {
    public Function(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid, boolean unique,
            boolean isSkolemConstant) {
        super(name, argSorts, sort, whereToBind, toModifier(isRigid, unique, isSkolemConstant));
    }

    private static Modifier toModifier(boolean isRigid, boolean unique, boolean isSkolemConstant) {
        Modifier mod = Modifier.NONE;
        if (isRigid)
            mod = mod.combine(Modifier.RIGID);
        if (unique)
            mod = mod.combine(Modifier.UNIQUE);
        if (isSkolemConstant)
            mod = mod.combine(Modifier.SKOLEM);
        return mod;
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Indicates whether the function or predicate symbol has the "uniqueness" property. For two
     * unique symbols f1: A1 -> B1, f2: A2 -> B2 by definition we have (1) f1(x) != f1(y) for all x,
     * y in A1 with x != y (i.e., injectivity), and (2) f1(x) != f2(y) for all x in A1, y in A2.
     */
    public final boolean isUnique() {
        return hasModifier(Modifier.UNIQUE);
    }

    public final boolean isSkolemConstant() {
        return hasModifier(Modifier.SKOLEM);
    }

    @Override
    public final String toString() {
        return (name() + (whereToBind() == null ? "" : "{" + whereToBind() + "}"));
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Function " + name() + " has no children");
    }
}
