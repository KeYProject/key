/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

public interface IntIterator {
    /// @return Integer the next element of collection
    int next();

    /// @return boolean true iff collection has more unseen elements
    boolean hasNext();
}
