/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.GenericParameter;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Sorted;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class ParametricFunctionDecl implements Named, Sorted {
    private final Name name;
    private final ImmutableList<GenericParameter> parameters;
    private final ImmutableArray<Sort> argSorts;
    private final Sort sort;
    private final @Nullable ImmutableArray<Boolean> whereToBind;
    private final boolean unique;
    private final boolean isRigid;
    private final boolean isSkolemConstant;

    public ParametricFunctionDecl(Name name, ImmutableList<GenericParameter> parameters,
            ImmutableArray<Sort> argSorts, Sort sort,
            @Nullable ImmutableArray<Boolean> whereToBind, boolean unique, boolean isRigid,
            boolean isSkolemConstant) {
        this.name = name;
        this.parameters = parameters;
        this.argSorts = argSorts;
        this.sort = sort;
        this.whereToBind = whereToBind;
        this.unique = unique;
        this.isRigid = isRigid;
        this.isSkolemConstant = isSkolemConstant;
    }

    @Override
    public @NonNull Sort sort() {
        return sort;
    }

    public ImmutableArray<Sort> argSorts() {
        return argSorts;
    }

    public @Nullable ImmutableArray<Boolean> getWhereToBind() {
        return whereToBind;
    }

    public boolean isUnique() {
        return unique;
    }

    public boolean isRigid() {
        return isRigid;
    }

    public boolean isSkolemConstant() {
        return isSkolemConstant;
    }

    public ImmutableList<GenericParameter> getParameters() {
        return parameters;
    }

    @Override
    public @NonNull Name name() {
        return name;
    }
}
