/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * Abstract operator class offering some common functionality.
 */
public abstract class AbstractOperator<S extends Sort<S>, T extends Term> implements Operator<S, T> {
    private final Name name;
    private final int arity;
    private final ImmutableArray<Boolean> whereToBind;
    private final boolean isRigid;

    protected AbstractOperator(Name name, int arity, ImmutableArray<Boolean> whereToBind,
            boolean isRigid) {
        assert name != null;
        assert arity >= 0;
        assert whereToBind == null || whereToBind.size() == arity;
        this.name = name;
        this.arity = arity;
        this.whereToBind = whereToBind;
        this.isRigid = isRigid;
    }

    protected AbstractOperator(Name name, int arity, Boolean[] whereToBind, boolean isRigid) {
        this(name, arity, new ImmutableArray<>(whereToBind), isRigid);
    }

    protected AbstractOperator(Name name, int arity, boolean isRigid) {
        this(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }

    protected final ImmutableArray<Boolean> whereToBind() {
        return whereToBind;
    }

    @Override
    public final Name name() {
        return name;
    }

    @Override
    public final int arity() {
        return arity;
    }

    @Override
    public final boolean bindVarsAt(int n) {
        return whereToBind != null && whereToBind.get(n);
    }

    @Override
    public final boolean isRigid() {
        return isRigid;
    }

    @Override
    public String toString() {
        return name().toString();
    }
}
