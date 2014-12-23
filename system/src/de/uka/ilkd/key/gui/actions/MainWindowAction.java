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

import java.awt.Toolkit;

import javax.swing.*;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.KeyStrokeManager;

public abstract class MainWindowAction extends AbstractAction {

    /**
     *
     */
    private static final long serialVersionUID = -6611537258325987383L;

    /**
     * This constant holds the typical key to be used for shortcuts (usually
     * {@link java.awt.Event#CTRL_MASK})
     */
    protected static final int SHORTCUT_KEY_MASK
            = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();

    protected final MainWindow mainWindow;

    protected MainWindowAction(MainWindow mainWindow) {
        assert mainWindow != null;
        this.mainWindow = mainWindow;
        putValue(ACCELERATOR_KEY, KeyStrokeManager.get(this));
    }
    
    protected KeYMediator getMediator() {
        return mainWindow.getMediator();
    }

    protected void setName(String name) {
        putValue(NAME, name);
    }

    protected String getName() {
        return (String) getValue(NAME);
    }

    @Deprecated // add a line in gui.utils.KeyStrokeManager instead
    protected void setAcceleratorLetter(int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    @Deprecated // add a line in gui.utils.KeyStrokeManager instead
    protected void setAcceleratorKey(KeyStroke keyStroke) {
        putValue(ACCELERATOR_KEY, keyStroke);
    }

    protected void setTooltip(String toolTip) {
        putValue(Action.SHORT_DESCRIPTION, toolTip);
    }

    protected void setIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

    protected void setSelected(Boolean b) {
        putValue(SELECTED_KEY, b);
    }

    protected boolean isSelected() {
        return getValue(SELECTED_KEY) == Boolean.TRUE;
    }
}
