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
