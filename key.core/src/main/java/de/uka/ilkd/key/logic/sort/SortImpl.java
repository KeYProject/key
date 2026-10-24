/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic.sort;

import java.util.Objects;

import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Abstract base class for implementations of the Sort interface.
 */
@NullMarked
public class SortImpl extends AbstractSort {
    // NullSort passes a literal {@code null} through the constructor, so this field is genuinely
    // nullable; {@link #extendsSorts()} narrows it again before dereferencing.
    private @Nullable ImmutableSet<Sort> ext;

    public SortImpl(Name name, @Nullable ImmutableSet<Sort> ext, boolean isAbstract) {
        super(name, isAbstract);
        this.ext = ext;
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext) {
        this(name, ext, false);
    }

    public SortImpl(Name name, Sort ext) {
        this(name, DefaultImmutableSet.<Sort>nil().add(ext), false);
    }

    public SortImpl(Name name) {
        this(name, DefaultImmutableSet.nil());
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        if (this == JavaDLTheory.FORMULA || this == JavaDLTheory.UPDATE
                || this == JavaDLTheory.ANY) {
            return DefaultImmutableSet.nil();
        } else {
            ImmutableSet<Sort> result =
                Objects.requireNonNull(ext, "extends sorts must not be null here");
            if (result.isEmpty()) {
                result = result.add(JavaDLTheory.ANY);
                ext = result;
            }
            return result;
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
    public boolean containsGenericSort() {
        return false;
    }
}
