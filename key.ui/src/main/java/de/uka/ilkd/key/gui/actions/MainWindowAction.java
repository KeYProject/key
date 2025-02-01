/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import static de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager.SHORTCUT_KEY_MASK;

/**
 * {@link KeyAction} extended to automatically override the accelerator key after the default is
 * set using {@link #setAcceleratorKey(KeyStroke)} / {@link #setAcceleratorLetter(int)} using the
 * {@link KeyStrokeManager}.
 */
public abstract class MainWindowAction extends KeyAction {
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
            enabledOnAnActiveProof();
        }
    }

    protected final void enabledOnAnActiveProof() {
        updateEnablednessOnSelectionChange();
        this.setEnabledWhen(this.getEnabledWhen().and(this::isProofSelected));
    }

    protected final void enabledWhenNotInAutoMode() {
        updateEnablednessOnAutoModeChange();
        Pred isMainWindowAutoMode = this::isMainWindowAutoMode;
        this.setEnabledWhen(this.getEnabledWhen().and(isMainWindowAutoMode.not()));
    }


    /// Method returns true iff a proof is currently selected.
    /// Useful as a predicate for [#setEnabledWhen].
    /// ```java
    /// setEnabledWhen(this::isProofSelected);
    ///```
    protected final boolean isProofSelected() {
        return getMediator().getSelectionModel().getSelectedProof() != null;
    }

    /// Method returns true iff the auto-mode or any other macro application is running.
    /// Useful as a predicate for [#setEnabledWhen].
    /// ```java
    /// setEnabledWhen(not(this::isMainWindowAutoMode));
    ///```
    protected final boolean isMainWindowAutoMode() {
        return mainWindow.isInAutoMode();
    }

    /**
     * This method adds a selection to the main window, s.t., the enabledness is updated when
     * the selection of proof or node is changed.
     */
    protected final void updateEnablednessOnSelectionChange() {
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                updateEnabledness();
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                updateEnabledness();
            }
        });
    }

    /// This methods places a {@link #java.beans.PropertyChangeListener}, s.t.,
    /// the enabledness is updated when the auto-mode/macro is executed or finished in side the [#mainWindow].
    protected final void updateEnablednessOnAutoModeChange() {
        mainWindow.addPropertyChangeListener(MainWindow.PROPERTY_IN_AUTO_MODE,
                p -> updateEnabledness());
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
}

        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
            var enable = e.getSource().getSelectedProof() != null;
            actions.forEach(a -> a.setEnabled(enable));
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
            var enable = e.getSource().getSelectedProof() != null;
            actions.forEach(a -> a.setEnabled(enable));
        }
    }
}
