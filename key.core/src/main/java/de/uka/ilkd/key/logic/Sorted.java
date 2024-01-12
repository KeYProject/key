/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.sort.Sort;

public interface Sorted {
    /**
     * the sort of the entity
     *
     * @return the {@link Sort} of the sorted entity
     */
    Sort sort();
}
