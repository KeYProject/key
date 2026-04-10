/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ViewSelector;

public class ToolTipOptionsAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = -360744615149278733L;

    public ToolTipOptionsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("ToolTip Options");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        ViewSelector vselector = new ViewSelector(mainWindow);
        vselector.setVisible(true);
    }
}
