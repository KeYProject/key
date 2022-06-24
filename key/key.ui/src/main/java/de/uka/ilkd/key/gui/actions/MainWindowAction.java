package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;

import javax.swing.*;

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
