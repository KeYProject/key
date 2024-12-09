/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.util.ArrayList;
import java.util.Collection;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;

import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.SHORTCUT_KEY_MASK;

/**
 * {@link KeyAction} extended to automatically override the accelerator key after the default is
 * set using {@link #setAcceleratorKey(KeyStroke)} / {@link #setAcceleratorLetter(int)} using the
 * {@link KeyStrokeManager}.
 */
public abstract class MainWindowAction extends KeyAction {
    private static final long serialVersionUID = -6611537258325987383L;

    private static final MainWindowActionSelectionListener LISTENER =
        new MainWindowActionSelectionListener();

    protected final MainWindow mainWindow;

    protected MainWindowAction(MainWindow mainWindow) {
        assert mainWindow != null;
        this.mainWindow = mainWindow;
        putValue(ACCELERATOR_KEY, KeyStrokeManager.get(this));
        KeyStrokeManager.registerAction(this);
    }

    protected MainWindowAction(MainWindow mainWindow, boolean onlyActiveWhenProofAvailable) {
        this(mainWindow);
        if (onlyActiveWhenProofAvailable) {
            LISTENER.addAction(this);
            this.setEnabled(getMediator().getSelectionModel().getSelectedProof() != null);
        }
    }

    @Override
    protected void setAcceleratorLetter(int letter) {
        setAcceleratorKey(KeyStroke.getKeyStroke(letter, SHORTCUT_KEY_MASK));
    }

    @Override
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

    private static final class MainWindowActionSelectionListener implements KeYSelectionListener {
        private final Collection<MainWindowAction> actions = new ArrayList<>();

        private void addAction(MainWindowAction action) {
            if (actions.isEmpty()) {
                action.getMediator().addKeYSelectionListener(this);
            }
            actions.add(action);
        }

        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            var enable = e.getSource().getSelectedProof() != null;
            actions.forEach(a -> a.setEnabled(enable));
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            selectedNodeChanged(e);
        }
    }
}
