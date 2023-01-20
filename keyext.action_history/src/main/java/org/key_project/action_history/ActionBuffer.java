package org.key_project.action_history;

import de.uka.ilkd.key.gui.UserAction;

import javax.swing.*;
import java.awt.*;
import java.util.List;

/**
 * Simple combobox to display the actions performed by the user. Selecting a particular entry
 * does not have any effect.
 *
 * @author Arne Keller
 */
public class ActionBuffer extends JComboBox<String> {
    /**
     * Construct a new action buffer.
     *
     * @param userActions list of user actions to display
     */
    public ActionBuffer(List<UserAction> userActions) {
        super();
        setUserActions(userActions);
    }

    @Override
    public Dimension getPreferredSize() {
        // limit size of toolbar entry so it is always visible
        Dimension preferred = super.getPreferredSize();
        return new Dimension(Math.min(preferred.width, 200), preferred.height);
    }

    /**
     * Show the provided list of user actions.
     *
     * @param userActions user actions to show
     */
    public void setUserActions(List<UserAction> userActions) {
        removeAllItems();
        for (int i = userActions.size() - 1; i >= 0; i--) {
            String name = userActions.get(i).name();
            addItem(name);
        }
    }
}
