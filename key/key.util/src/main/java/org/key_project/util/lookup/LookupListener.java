/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package org.key_project.util.lookup;

/**
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public interface LookupListener {
    void update(Class<?> clazz, Lookup lookup);
}
