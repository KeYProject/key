/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.sort;

import org.key_project.logic.HasOrigin;
import org.key_project.logic.LogicServices;
import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

public interface Sort extends Named, HasOrigin {
    /**
     * Gives the set of sorts that are direct super-sorts of this sort.
     *
     * The NullSort implementation fails on this method.
     *
     * @return a non-null set of sorts.
     */
    ImmutableSet<Sort> extendsSorts();

    /**
     * Gives the set of sorts that are direct super-sorts of this sort.
     *
     * The NullSort implementation does not fail on this method.
     *
     * By default, this method calls {@link #extendsSorts()}.
     *
     * @param services the logic services to use for computing super-sorts.
     * @return a non-null set of sorts.
     */
    default <Services extends LogicServices> ImmutableSet<Sort> extendsSorts(Services services) {
        return extendsSorts();
    }

    /**
     * Check whether this sort is a direct or indirect subsort of the given sort.
     *
     * @param sort some sort.
     * @return whether the given sort is a reflexive, transitive subsort of this sort.
     */
    boolean extendsTrans(Sort sort);

    /**
     * @return whether this sort has no exact elements.
     */
    boolean isAbstract();

    String declarationString();

    /**
     * Returns a human explainable text describing this sort.
     * This field is typically set by the
     * parser, who captures the documentation comments.
     */
    default @Nullable String getDocumentation() { return null; }
}
