/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import javax.swing.*;

/**
 * @author Alexander Weigl
 * @date 2019-04-11
 */
public class InvalidSettingsInputException extends Exception {
    private static final long serialVersionUID = -7504257775646675899L;
    private final SettingsProvider panel;
    private final JComponent focusable;

    public InvalidSettingsInputException(SettingsProvider panel, JComponent focusable) {
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputException(String message, SettingsProvider panel,
            JComponent focusable) {
        super(message);
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputException(String message, Throwable cause, SettingsProvider panel,
            JComponent focusable) {
        super(message, cause);
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputException(Throwable cause, SettingsProvider panel,
            JComponent focusable) {
        super(cause);
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputException(String message, Throwable cause, boolean enableSuppression,
            boolean writableStackTrace, SettingsProvider panel, JComponent focusable) {
        super(message, cause, enableSuppression, writableStackTrace);
        this.panel = panel;
        this.focusable = focusable;
    }

    public SettingsProvider getPanel() {
        return panel;
    }

    public JComponent getFocusable() {
        return focusable;
    }
}
