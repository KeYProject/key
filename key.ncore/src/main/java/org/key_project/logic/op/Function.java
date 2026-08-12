/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import static org.key_project.logic.op.Function.FunctionKind.DEFINITIONAL_SKOLEM;
import static org.key_project.logic.op.Function.FunctionKind.ORDINARY;
import static org.key_project.logic.op.Function.FunctionKind.SKOLEM;

/// Objects of this class represent function and predicate symbols. Note that program variables are
/// a separate syntactic category, and not a type of function.
public abstract class Function extends AbstractSortedOperator {
    /// Kinds of function symbols
    public enum FunctionKind {
        /// a normal logic function or predicate symbol
        ORDINARY,
        /// a skolem constant
        SKOLEM,
        /// a skolem constant introduced as a definitional equation
        DEFINITIONAL_SKOLEM
    }

    /// Value of [#introductionTime()] when no introduction time is available (e.g. not a Skolem
    /// constant)
    protected static final int UNRECORDED = -1;

    /// The point in a proof branch at which this skolem constant was introduced, counted in
    /// rule applications, or [#UNRECORDED].
    private final int introductionTime;

    protected Function(Name name, ImmutableArray<Sort> argSorts, Sort sort,
            ImmutableArray<Boolean> whereToBind, boolean isRigid, boolean unique,
            FunctionKind kind, int introductionTime) {
        super(name, argSorts, sort, whereToBind, toModifier(isRigid, unique, kind));
        this.introductionTime = introductionTime;
    }

    private static Modifier toModifier(boolean isRigid, boolean unique, FunctionKind kind) {
        Modifier mod = Modifier.NONE;
        if (isRigid)
            mod = mod.combine(Modifier.RIGID);
        if (unique)
            mod = mod.combine(Modifier.UNIQUE);
        if (kind != ORDINARY)
            mod = mod.combine(Modifier.SKOLEM);
        if (kind == DEFINITIONAL_SKOLEM)
            mod = mod.combine(Modifier.DEFINITIONAL_SKOLEM);
        return mod;
    }

    /// @return the kind of this symbol
    public final FunctionKind kind() {
        if (hasModifier(Modifier.DEFINITIONAL_SKOLEM)) {
            return DEFINITIONAL_SKOLEM;
        }
        return hasModifier(Modifier.SKOLEM) ? SKOLEM : ORDINARY;
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /// Indicates whether the function or predicate symbol has the "uniqueness" property. For two
    /// unique symbols f1: A1 -> B1, f2: A2 -> B2 by definition we have (1) f1(x) != f1(y) for all
    /// x, y in A1 with x != y (i.e., injectivity), and (2) f1(x) != f2(y) for all x in A1, y in A2.
    public final boolean isUnique() {
        return hasModifier(Modifier.UNIQUE);
    }

    public final boolean isSkolemConstant() {
        return hasModifier(Modifier.SKOLEM);
    }

    /// Whether this symbol is a definitional skolem symbol, one that abbreviates a term
    /// through a defining equation. A term ordering places such a symbol below all symbols
    /// that existed when it was made, so that applying its definition is a decrease.
    public final boolean isDefinitionalSkolem() {
        return hasModifier(Modifier.DEFINITIONAL_SKOLEM);
    }

    /// The point in a proof branch at which this skolem constant was introduced, counted in
    /// rule applications.
    ///
    /// @return the introduction time, or a negative value if none is recorded
    public final int introductionTime() {
        return introductionTime;
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
