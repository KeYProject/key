/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

import org.checkerframework.checker.nullness.qual.NonNull;

public final class ReferenceType implements Type {
    private final boolean isMut;
    private final Type inner;
    private final Name name;

    static final Map<Type, ReferenceType> shared = new HashMap<>();
    static final Map<Type, ReferenceType> mut = new HashMap<>();

    public static ReferenceType get(Type inner, boolean isMut) {
        var map = isMut ? mut : shared;
        return map.computeIfAbsent(inner, i -> new ReferenceType(isMut, inner));
    }

    private ReferenceType(boolean isMut, Type inner) {
        this.isMut = isMut;
        this.inner = inner;
        String pre = isMut ? "MRef_" : "Ref_";
        name = new Name(pre + inner.toString());
    }

    @Override
    public Sort getSort(Services services) {
        return services.getNamespaces().sorts().lookup(name);
    }

    @Override
    public @NonNull Name name() {
        return name;
    }

    public boolean isMut() {
        return isMut;
    }

    public Type inner() {
        return inner;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (ReferenceType) obj;
        return this.isMut == that.isMut &&
                Objects.equals(this.inner, that.inner);
    }

    @Override
    public int hashCode() {
        return Objects.hash(isMut, inner);
    }

    @Override
    public String toString() {
        return name.toString();
    }

}
