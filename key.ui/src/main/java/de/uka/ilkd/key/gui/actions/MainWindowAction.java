/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;

/**
 * {@link KeyAction} extended to automatically override the accelerator key after the default is
 * set using {@link #setAcceleratorKey(KeyStroke)} / {@link #setAcceleratorLetter(int)} using the
 * {@link KeyStrokeManager}.
 */
public abstract class MainWindowAction extends KeyAction {
    /**
     *
     */
    private static final long serialVersionUID = -6611537258325987383L;

    protected final MainWindow mainWindow;

    protected MainWindowAction(MainWindow mainWindow) {
        assert mainWindow != null;
        this.mainWindow = mainWindow;
        putValue(ACCELERATOR_KEY, KeyStrokeManager.get(this));
        KeyStrokeManager.registerAction(this);
    }

    protected void setAcceleratorLetter(int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    protected void setAcceleratorKey(KeyStroke keyStroke) {
        boolean trigger = getAcceleratorKey() == null;
        putValue(ACCELERATOR_KEY, keyStroke);
        if (trigger) {
            lookupAcceleratorKey();
        }
    }

    protected KeYMediator getMediator() {
        return mainWindow.getMediator();
    }
}
