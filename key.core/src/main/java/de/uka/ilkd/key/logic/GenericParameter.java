/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.sort.GenericSort;

import org.jspecify.annotations.NonNull;

/// Abstract parameter for [ParametricFunctionDecl] or [ParametricSortDecl]
public record GenericParameter(GenericSort sort, Variance variance) {
    @Override
    public @NonNull String toString() {
        return sort.toString();
    }

    public enum Variance {
        COVARIANT, CONTRAVARIANT, INVARIANT
    }
}
