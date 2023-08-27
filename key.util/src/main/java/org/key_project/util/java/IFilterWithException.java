/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

/**
 * Utility class to select elements which also allows that exceptions are thrown during selection
 * phase.
 *
 * @author Martin Hentschel
 */
public interface IFilterWithException<T, E extends Throwable> {
    /**
     * Checks if the given element should be selected.
     *
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     * @throws E An occurred exception.
     */
    boolean select(T element) throws E;
}
