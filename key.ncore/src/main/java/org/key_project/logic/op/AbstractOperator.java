/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.util.collection.ImmutableArray;

/**
 * Abstract operator class offering some common functionality.
 */
public abstract class AbstractOperator implements Operator {
    private final Name name;
    private final int arity;
    private final ImmutableArray<Boolean> whereToBind;
    private final Modifier modifier;

    protected AbstractOperator(Name name, int arity, ImmutableArray<Boolean> whereToBind,
            Modifier modifier) {
        assert name != null;
        assert arity >= 0;
        assert whereToBind == null || whereToBind.size() == arity;
        this.name = name;
        this.arity = arity;
        this.whereToBind = whereToBind;
        this.modifier = modifier;
    }

    protected AbstractOperator(Name name, int arity, ImmutableArray<Boolean> whereToBind,
            boolean isRigid) {
        this(name, arity, whereToBind, isRigid ? Modifier.RIGID : Modifier.NONE);
    }

    protected AbstractOperator(Name name, int arity, Boolean[] whereToBind, boolean isRigid) {
        this(name, arity, new ImmutableArray<>(whereToBind), isRigid);
    }

    protected AbstractOperator(Name name, int arity, boolean isRigid) {
        this(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }

    public final ImmutableArray<Boolean> whereToBind() {
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
    public final Modifier modifier() {
        return modifier;
    }

    @Override
    public final boolean isRigid() {
        return hasModifier(Modifier.RIGID);
    }

    @Override
    public String toString() {
        return name().toString();
    }

    /**
     * Checks whether the top level structure of the given @link Term is syntactically valid, given
     * the assumption that the top level operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal is NOT checked.
     *
     * @throws TermCreationException if a construction error was recognised
     */
    @Override
    public <T extends Term> void validTopLevelException(T term) throws TermCreationException {
        if (arity != term.arity()) {
            throw new TermCreationException(this, term);
        }

        if (arity != term.subs().size()) {
            throw new TermCreationException(this, term);
        }

        if ((whereToBind == null) != term.boundVars().isEmpty()) {
            throw new TermCreationException(this, term);
        }

        for (int i = 0; i < arity; i++) {
            if (term.sub(i) == null) {
                throw new TermCreationException(this, term);
            }
        }
    }

}
