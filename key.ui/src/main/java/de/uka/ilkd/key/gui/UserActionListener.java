/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.actions.useractions.UserAction;

/**
 * Listener for user actions.
 *
 * @see UserAction
 * @author Arne Keller
 */
public interface UserActionListener {
    /**
     * Handle a user action just performed by the user.
     *
     * @param action the user action
     */
    void actionPerformed(UserAction action);
}
