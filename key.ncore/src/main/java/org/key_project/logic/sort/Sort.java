/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.sort;

import jakarta.annotation.Nullable;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableSet;

public interface Sort<S extends Sort> extends Named {
    /**
     * Formulas are represented as "terms" of this sort.
     */
    Sort FORMULA = new SortImpl(new Name("Formula"));

    /**
     * Updates are represented as "terms" of this sort.
     */
    Sort UPDATE = new SortImpl(new Name("Update"));

    /**
     * Any is a supersort of all sorts.
     */
    Sort ANY = new SortImpl(new Name("any"));

    /**
     * @return the direct supersorts of this sort. Not supported by {@code NullSort}.
     */
    ImmutableSet<S> extendsSorts();

    /**
     * @param s some sort.
     * @return whether the given sort is a reflexive, transitive subsort of this sort.
     */
    boolean extendsTrans(S s);

    /**
     * @return whether this sort has no exact elements.
     */
    boolean isAbstract();

    String declarationString();

    /**
     * Returns an human explainable text describing this sort. This field is typical set by the
     * parser, who captures the documentation comments.
     */
    @Nullable
    default String getDocumentation() { return null; }


}
