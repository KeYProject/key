/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import javafx.scene.Node;

/**
 * Thrown by a {@link SettingsProviderF} if an input component is not properly filled; prevents
 * the settings dialog from closing, counter-part of {@code InvalidSettingsInputException} of the
 * Swing module {@code key.ui}.
 *
 * @author Alexander Weigl
 */
public class InvalidSettingsInputExceptionF extends Exception {

    /** the provider whose panel caused the error */
    private final transient SettingsProviderF panel;

    /** the input node that should receive the focus */
    private final transient Node focusable;

    public InvalidSettingsInputExceptionF(SettingsProviderF panel, Node focusable) {
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputExceptionF(String message, SettingsProviderF panel,
            Node focusable) {
        super(message);
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputExceptionF(String message, Throwable cause,
            SettingsProviderF panel, Node focusable) {
        super(message, cause);
        this.panel = panel;
        this.focusable = focusable;
    }

    public InvalidSettingsInputExceptionF(Throwable cause, SettingsProviderF panel,
            Node focusable) {
        super(cause);
        this.panel = panel;
        this.focusable = focusable;
    }

    /**
     * @return the provider whose panel caused the error
     */
    public SettingsProviderF getPanel() {
        return panel;
    }

    /**
     * @return the input node that should receive the focus
     */
    public Node getFocusable() {
        return focusable;
    }
}
