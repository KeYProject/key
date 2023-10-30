/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.rule.HasOrigin;

import org.key_project.logic.Name;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class Sort extends org.key_project.logic.sort.AbstractSort<Sort>
        implements HasOrigin {
    /**
     * Documentation for this sort given by the associated documentation comment.
     *
     * @see de.uka.ilkd.key.nparser.KeYParser.One_sort_declContext#doc
     */
    private final String documentation;

    /** Information of the origin of this sort */
    private final String origin;
    private ImmutableSet<Sort> ext;

    public Sort(Name name, ImmutableSet<Sort> ext, boolean isAbstract, String documentation,
            String origin) {
        super(name, isAbstract);
        this.ext = ext;
        this.documentation = documentation;
        this.origin = origin;
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

    public ImmutableSet<Sort> extendsSorts(Services services) {
        return extendsSorts();
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
