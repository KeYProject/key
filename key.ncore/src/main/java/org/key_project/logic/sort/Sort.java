/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.sort;

import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableSet;

import jakarta.annotation.Nullable;

public interface Sort<S extends Sort<S>> extends Named {
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
     * Returns a human explainable text describing this sort. This field is typical set by the
     * parser, who captures the documentation comments.
     */
    @Nullable
    default String getDocumentation() { return null; }
}
