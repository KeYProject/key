/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import org.checkerframework.checker.nullness.qual.KeyForBottom;
import org.jspecify.annotations.Nullable;

/**
 * This interface declares a tupel of two values. The first one is of type <S> and named key, the
 * second one is of type <T> and named value
 *
 * For type annotations see Florian Lanzinger or Werner Dietl. :)
 * https://eisop.github.io/cf/manual/manual.html#map-key-defaults-lowerbound
 */

public interface ImmutableMapEntry<@KeyForBottom S, @KeyForBottom T extends @Nullable Object> {

    /** @return the first part of the tupel */
    S key();

    /** @return the second part of the tupel */
    T value();
}
