/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.toolbar;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.jspecify.annotations.NullMarked;

/**
 * Action to enable/disable Proof Caching.
 *
 * @author Arne Keller
 */
@NullMarked
public class CachingToggleAction extends MainWindowAction {
    public static final Icon ICON =
        IconFactory.keyCachedClosed((int) IconFactory.DEFAULT_SIZE, (int) IconFactory.DEFAULT_SIZE);
    private static final String DESCRIPTION =
        "Enable or disable proof caching for currently open proofs.";

    /**
     * The setters below are called on {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since all fields are set before
     * the calls, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public CachingToggleAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Proof Caching");
        setMenuPath("Options");
        setEnabled(true);
        setSelected(true);
        putValue(LONG_DESCRIPTION, DESCRIPTION);
        // for main menu variant of action
        putValue(CHECKBOX, true);
        setTooltip(DESCRIPTION);

        setIcon(ICON);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        // no action, status of checkbox is checked in extension class
    }
}
