/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * This class can be used for adding Checkboxes to the menu.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class KeYMenuCheckBox extends JCheckBoxMenuItem {

    /**
     *
     */
    private static final long serialVersionUID = -4156054085757784178L;
    protected final MainWindowAction mainWindowAction;

    /*
     * If this constructor is used, default selected state for the CheckBox is false.
     */
    KeYMenuCheckBox(MainWindow mainWindow, String label) {
        this(mainWindow, label, false);
    }

    KeYMenuCheckBox(MainWindow mainWindow, String label, boolean selectedState) {
        super("", selectedState);
        final KeYMenuCheckBox checkBox = this;
        mainWindowAction = new MainWindowAction(mainWindow) {
            /**
             *
             */
            private static final long serialVersionUID = -8553172978879292800L;

            @Override
            public void actionPerformed(ActionEvent ae) {
                handleClickEvent();
                mainWindow.savePreferences(checkBox);
            }
        };
        mainWindowAction.setName(label);
        setAction(mainWindowAction);
    }

    public void setTooltip(String s) {
        mainWindowAction.setTooltip(s);
    }

    /*
     * Make sure getState() does the same as isSelected().
     */
    @Override
    public boolean getState() {
        return isSelected();
    }

    /*
     * Make sure setState(boolean) does the same as setSelected(boolean).
     */
    @Override
    public void setState(boolean b) {
        setSelected(b);
    }

    public abstract void handleClickEvent();
}
