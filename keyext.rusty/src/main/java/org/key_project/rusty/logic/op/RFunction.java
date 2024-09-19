/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.util.collection.ImmutableArray;

public class RFunction extends Function {
    RFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isRigid,
            boolean isSkolemConstant) {
        super(name, argSorts, sort, whereToBind, isRigid, unique, isSkolemConstant);

        assert sort != RustyDLTheory.UPDATE;
        assert !(unique && sort == RustyDLTheory.FORMULA);
    }

    public RFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique) {
        this(name, sort, argSorts, whereToBind, unique, true, false);
    }

    public RFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts,
            ImmutableArray<Boolean> whereToBind, boolean unique, boolean isSkolemConstant) {
        this(name, sort, argSorts, whereToBind, unique, true, isSkolemConstant);
    }

    public RFunction(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind,
            boolean unique) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique);
    }

    public RFunction(Name name, Sort sort, Sort[] argSorts, Boolean[] whereToBind,
            boolean unique,
            boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(argSorts),
            whereToBind == null ? null : new ImmutableArray<>(whereToBind), unique,
            isSkolemConstant);
    }

    RFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts, boolean isRigid) {
        this(name, sort, argSorts, null, false, isRigid, false);
    }

    public RFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public RFunction(Name name, Sort sort, Sort... argSorts) {
        this(name, sort, argSorts, null, false);
    }

    public RFunction(Name name, Sort sort, boolean isSkolemConstant, Sort... argSorts) {
        this(name, sort, argSorts, null, false, isSkolemConstant);
    }

    public RFunction(Name name, Sort sort) {
        this(name, sort, new ImmutableArray<>(), null, false);
    }

    public RFunction(Name name, Sort sort, boolean isSkolemConstant) {
        this(name, sort, new ImmutableArray<>(), null, false, true, isSkolemConstant);
    }
}
