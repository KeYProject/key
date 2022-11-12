/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package org.key_project.util.collection;

/**
 * This interface declares a tupel of two values. The first one is of type <S> and named key, the
 * second one is of type <T> and named value
 */

public interface ImmutableMapEntry<S, T> extends java.io.Serializable {

    /** @return the first part of the tupel */
    S key();

    /** @return the second part of the tupel */
    T value();
}
