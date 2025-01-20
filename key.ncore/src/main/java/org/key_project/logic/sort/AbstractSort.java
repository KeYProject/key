/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.sort;

import org.key_project.logic.Name;

import org.jspecify.annotations.Nullable;


/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort implements Sort {
    private final Name name;
    private final boolean isAbstract;

    /**
     * Documentation for this sort given by the associated documentation comment.
     * //@see de.uka.ilkd.key.nparser.KeYParser.One_sort_declContext#doc
     */
    private @Nullable String documentation;

    public AbstractSort(Name name, boolean isAbstract) {
        this.name = name;
        this.isAbstract = isAbstract;
    }

    public boolean equals(@Nullable Object o) {
        if (o instanceof AbstractSort sort) {
            // TODO: Potential bug should check for sort identity not name equality
            return sort.name().equals(name());
        } else {
            return false;
        }
    }

    @Override
    public final Name name() {
        return name;
    }

    @Override
    public final boolean isAbstract() {
        return isAbstract;
    }

    @Override
    public final String toString() {
        return name.toString();
    }

    public String declarationString() {
        return name.toString();
    }

    public void setDocumentation(@Nullable String documentation) {
        this.documentation = documentation;
    }

    @Override
    public @Nullable String getDocumentation() {
        return documentation;
    }
}
