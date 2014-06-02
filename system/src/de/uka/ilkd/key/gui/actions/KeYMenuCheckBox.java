// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

/**
 * This class can be used for adding Checkboxes to the menu.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public abstract class KeYMenuCheckBox extends JCheckBoxMenuItem {

    protected final MainWindowAction mainWindowAction;

    KeYMenuCheckBox(MainWindow mainWindow, String label) {
        final KeYMenuCheckBox checkBox = this;
        mainWindowAction = new MainWindowAction(mainWindow) {
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