/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

/**
 * Simple interface to be notified about all changes to the selection history.
 *
 * @author Arne Keller
 */
public interface SelectionHistoryChangeListener {
    /**
     * Update state. Called whenever the history is modified.
     */
    void update();
}
