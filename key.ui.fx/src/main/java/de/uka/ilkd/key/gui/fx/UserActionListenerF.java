/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import de.uka.ilkd.key.gui.fx.actions.useractions.UserActionF;

import org.jspecify.annotations.NullMarked;

/**
 * Listener for user actions, FX counterpart of
 * {@code de.uka.ilkd.key.gui.UserActionListener} (Swing UserActionListener.java:1-21).
 *
 * @see UserActionF
 */
@NullMarked
@FunctionalInterface
public interface UserActionListenerF {

    /**
     * Handle a user action just performed by the user.
     *
     * @param action the user action
     */
    void actionPerformed(UserActionF action);
}
