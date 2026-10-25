/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import org.jspecify.annotations.NullMarked;

/**
 * Simple interface to be notified about all changes to the selection history.
 *
 * @author Arne Keller
 */
@NullMarked
public interface SelectionHistoryChangeListener {
    /**
     * Update state. Called whenever the history is modified.
     */
    void update();
}
