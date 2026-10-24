/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key;

import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.23)
 */
@NullMarked
public interface Identifiable {
    default String identification() {
        return getClass().getName() + "_" + hashCode();
    }
}
