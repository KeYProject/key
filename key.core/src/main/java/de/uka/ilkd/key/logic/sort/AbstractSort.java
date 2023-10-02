/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort extends org.key_project.logic.sort.AbstractSort<Sort>
        implements Sort {
    private ImmutableSet<Sort> ext;

    /**
     * Documentation for this sort given by the associated documentation comment.
     *
     * @see de.uka.ilkd.key.nparser.KeYParser.One_sort_declContext#doc
     */
    private final String documentation;

    /** Information of the origin of this sort */
    private final String origin;

    public AbstractSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract, String documentation,
            String origin) {
        super(name, isAbstract);
        this.ext = ext;
        this.documentation = documentation;
        this.origin = origin;
    }

    @Override
    public final ImmutableSet<Sort> extendsSorts() {
        if (this == Sort.FORMULA || this == Sort.UPDATE || this == Sort.ANY) {
            return DefaultImmutableSet.nil();
        } else {
            if (ext.isEmpty()) {
                ext = DefaultImmutableSet.<Sort>nil().add(Sort.ANY);
            }
            return ext;
        }
    }

    @Override
    public final ImmutableSet<Sort> extendsSorts(Services services) {
        return extendsSorts();
    }


    @Override
    public final boolean extendsTrans(Sort sort) {
        if (sort == this) {
            return true;
        } else if (this == Sort.FORMULA || this == Sort.UPDATE) {
            return false;
        } else if (sort == Sort.ANY) {
            return true;
        }

        return extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }

    public String declarationString() {
        return name().toString();
    }

    @Nullable
    @Override
    public String getDocumentation() {
        return documentation;
    }

    @Nullable
    @Override
    public String getOrigin() {
        return origin;
    }
}
