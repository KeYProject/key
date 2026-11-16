/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.settings;

import org.jspecify.annotations.NullMarked;

@NullMarked
public interface Validator<T> {
    void validate(T obj) throws Exception;
}
