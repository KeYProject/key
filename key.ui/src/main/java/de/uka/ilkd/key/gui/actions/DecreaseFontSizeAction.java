/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

public class DecreaseFontSizeAction extends MainWindowAction implements ConfigChangeListener {

    /**
     * generated sUID
     */
    private static final long serialVersionUID = 8774824535047619737L;

    /**
     * creates the action to decrease the font size of the sequent and proof view
     *
     * @param mainWindow the main window
     */
    public DecreaseFontSizeAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Smaller");
        setIcon(IconFactory.minus(16));

        Config.DEFAULT.addConfigChangeListener(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Config.DEFAULT.smaller();
    }

    @Override
    public void configChanged(ConfigChangeEvent e) {
        setEnabled(!Config.DEFAULT.isMinimumSize());
    }

}
