/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.sort;

import org.key_project.logic.HasDocumentation;
import org.key_project.logic.HasOrigin;
import org.key_project.logic.LogicServices;
import org.key_project.logic.Named;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

public interface Sort extends Named, HasOrigin, HasDocumentation {
    /// @return the direct supersorts of this sort. Not supported by `NullSort`.
    ImmutableSet<Sort> extendsSorts();

    default <Services extends LogicServices> ImmutableSet<Sort> extendsSorts(Services services) {
        return extendsSorts();
    }

    /// @param s some sort.
    /// @return whether the given sort is a reflexive, transitive subsort of this sort.
    boolean extendsTrans(Sort s);

    /// @return whether this sort has no exact elements.
    boolean isAbstract();

    String declarationString();

    @Override
    default String getDocumentationKey(){
        return "sort/" + name();
    }
}
