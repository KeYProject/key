/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

/**
 * Utility class to select elements.
 *
 * @author Martin Hentschel
 */
public interface IFilter<T> {
    /**
     * Checks if the given element should be selected.
     *
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     */
    boolean select(T element);
}
