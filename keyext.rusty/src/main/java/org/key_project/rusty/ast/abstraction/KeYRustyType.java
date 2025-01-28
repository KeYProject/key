/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import java.util.Objects;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.ty.SortRustType;

import org.jspecify.annotations.NonNull;

public class KeYRustyType implements Type {
    /** the AST type */
    private Type rustyType = null;
    /** the logic sort */
    private Sort sort = null;

    public KeYRustyType() {
    }

    public KeYRustyType(Type rustyType, Sort sort) {
        this.rustyType = rustyType;
        this.sort = sort;
    }

    public KeYRustyType(Type rustyType) {
        this.rustyType = rustyType;
    }

    public KeYRustyType(Sort sort) {
        this.sort = sort;
    }

    @Override
    public Sort getSort(Services services) {
        return sort;
    }

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public Type getRustyType() {
        return rustyType;
    }

    public void setRustyType(Type rustyType) {
        this.rustyType = rustyType;
    }

    @Override
    public @NonNull Name name() {
        return rustyType == null ? sort.name() : rustyType.name();
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }
        try {
            return Objects.equals(rustyType, ((KeYRustyType) o).rustyType)
                    && Objects.equals(sort, ((KeYRustyType) o).sort);
        } catch (Exception e) {
            return false;
        }
    }

    @Override
    public RustType toRustType(Services services) {
        if (rustyType == null) {
            return new SortRustType(this);
        }
        return rustyType.toRustType(services);
    }
}
