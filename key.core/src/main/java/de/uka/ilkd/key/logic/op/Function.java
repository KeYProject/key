/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.ImmutableArray;


/**
 * Objects of this class represent function and predicate symbols. Note that program variables are a
 * separate syntactic category, and not a type of function.
 */
public class Function extends AbstractSortedOperator {

    private final boolean unique;
    private final boolean skolemConstant;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    Function(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isRigid,
            boolean isSkolemConstant) {
        super(name, argSorts, sort, whereToBind, isRigid);

        this.unique = unique;
        skolemConstant = isSkolemConstant;
        assert sort != Sort.UPDATE;
        assert !(unique && sort == Sort.FORMULA);
        assert !(sort instanceof NullSort) || name.toString().equals("null")
                : "Functions with sort \"null\" are not allowed: " + this;
    }

    public Function(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique) {
        this(name, sort, argSorts, whereToBind, unique, true, false);
    }

    public Function(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isSkolemConstant) {
        this(name, sort, argSorts, whereToBind, unique, true, isSkolemConstant);
    }

    public Function(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind, boolean unique) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique);
    }

    public Function(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind, boolean unique,
            boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique,
            isSkolemConstant);
    }

    Function(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isRigid) {
        this(name, sort, argSorts, null, false, isRigid, false);
    }

    public Function(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public Function(Name name, Sort sort, Sort... argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public Function(Name name, Sort sort, boolean isSkolemConstant, Sort... argSorts) {
        this(name, sort, argSorts, null, false, isSkolemConstant);
    }

    public Function(Name name, Sort sort) {
        this(name, sort, new ImmutableArray<>(), null, false);
    }

    public Function(Name name, Sort sort, boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(), null, false, true, isSkolemConstant);
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
        return unique;
    }

    public final boolean isSkolemConstant() {
        return skolemConstant;
    }

    @Override
    public final String toString() {
        return (name() + (whereToBind() == null ? "" : "{" + whereToBind() + "}"));
    }

    /**
     * Returns a parsable string representation of the declaration of this function or predicate
     * symbol.
     */
    public final String proofToString() {
        StringBuilder s =
            new StringBuilder((sort() == Sort.FORMULA ? "" : sort().toString()) + " ");
        s.append(name());
        if (arity() > 0) {
            int i = 0;
            s.append("(");
            while (i < arity()) {
                if (i > 0) {
                    s.append(",");
                }
                s.append(argSort(i));
                i++;
            }
            s.append(")");
        }
        s.append(";\n");
        return s.toString();
    }

    public Function rename(Name newName) {
        return new Function(newName, sort(), argSorts(), whereToBind(), unique, skolemConstant);
    }
}
