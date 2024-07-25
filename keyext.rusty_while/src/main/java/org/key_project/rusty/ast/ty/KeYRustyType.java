/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.ty;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

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
}
