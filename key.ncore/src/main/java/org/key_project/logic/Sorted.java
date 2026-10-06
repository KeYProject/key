/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.logic;

import org.key_project.logic.sort.Sort;

public interface Sorted {
    /// the sort of the entity
    ///
    /// @return the [Sort] of the sorted entity
    Sort sort();
}
