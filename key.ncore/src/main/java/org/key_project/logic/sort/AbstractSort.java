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
    private String documentation;

    public AbstractSort(Name name, boolean isAbstract) {
        this.name = name;
        this.isAbstract = isAbstract;
    }

    // @Override
    // public final ImmutableSet<S> extendsSorts() {
    // if (this == Sort.FORMULA || this == Sort.UPDATE || this == Sort.ANY) {
    // return DefaultImmutableSet.nil();
    // } else {
    // if (ext.isEmpty()) {
    // ext = DefaultImmutableSet.<S>nil().add((S)ANY);
    // }
    // return ext;
    // }
    // }

    // @Override
    // public final boolean extendsTrans(S sort) {
    // if (sort == this) {
    // return true;
    // } else if (this == Sort.FORMULA || this == Sort.UPDATE) {
    // return false;
    // } else if (sort == Sort.ANY) {
    // return true;
    // }
    //
    // return extendsSorts()
    // .exists((S superSort) -> superSort == sort || superSort.extendsTrans(sort));
    // }

    public boolean equals(Object o) {
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

    @Nullable
    @Override
    public String getDocumentation() {
        return documentation;
    }
}
