/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public class SortImpl extends org.key_project.logic.sort.AbstractSort {
    /**
     * Documentation for this sort given by the associated documentation comment.
     *
     * @see de.uka.ilkd.key.nparser.KeYParser.One_sort_declContext#doc
     */
    private final String documentation;

    /** Information of the origin of this sort */
    private final String origin;
    private ImmutableSet<Sort> ext;

    public SortImpl(Name name, ImmutableSet<Sort> ext, boolean isAbstract, String documentation,
            String origin) {
        super(name, isAbstract);
        this.ext = ext;
        this.documentation = documentation;
        this.origin = origin;
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext, String documentation, String origin) {
        this(name, ext, false, documentation, origin);
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
        this(name, ext, isAbstract, "", "");
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext) {
        this(name, ext, false, "", "");
    }

    public SortImpl(Name name, Sort ext) {
        this(name, DefaultImmutableSet.<Sort>nil().add(ext), false, "", "");
    }


    public SortImpl(Name name) {
        this(name, DefaultImmutableSet.nil(), "", "");
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        if (this == JavaDLTheory.FORMULA || this == JavaDLTheory.UPDATE
                || this == JavaDLTheory.ANY) {
            return DefaultImmutableSet.nil();
        } else {
            if (ext.isEmpty()) {
                ext = DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY);
            }
            return ext;
        }
    }

    @Override
    public boolean extendsTrans(Sort sort) {
        if (sort == this) {
            return true;
        } else if (this == JavaDLTheory.FORMULA || this == JavaDLTheory.UPDATE) {
            return false;
        } else if (sort == JavaDLTheory.ANY) {
            return true;
        }

        return extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }

    public String declarationString() {
        return name().toString();
    }

    @Override
    public @Nullable String getDocumentation() {
        return documentation;
    }

    @Override
    public @Nullable String getOrigin() {
        return origin;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof SortImpl) {
            return ((SortImpl) o).name().equals(name());
        } else {
            return false;
        }
    }
}
