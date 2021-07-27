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
     * If this constructor is used, default selected state for the CheckBox
     * is false.
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
