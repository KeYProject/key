/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts.meta;

/**
 * A {@link Converter} translates an instance of {@code R} to an instance of {@code T}.
 *
 * @param <R> the result type
 * @param <T> the source type
 * @author Alexander Weigl
 */
public interface Converter<R, T> {
    /**
     * Translates one representation given in {@code s} to an instance of {@code R}.
     *
     * @param s a non-null argument to convert
     * @return a corresponding instance of T after conversion
     * @throws Exception if there is an error during the translation (format incorrect etc ...)
     */
    R convert(T s) throws Exception;
}
