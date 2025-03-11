/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;


import java.awt.event.ActionEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

public class PrettyPrintToggleAction extends MainWindowAction {
    public static final String NAME = "Use Pretty Syntax";

    public static final String TOOL_TIP = "If ticked, infix notations are used.";

    /**
     *
     */
    private static final long serialVersionUID = 8633254204256247698L;

    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     */
    private final PropertyChangeListener viewSettingsListener = this::handleViewSettingsChanged;

    public PrettyPrintToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOL_TIP);
        // Attention: The listener is never
        // removed, because there is only one
        // MainWindow!
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(ViewSettings.PRETTY_SYNTAX, viewSettingsListener);
        updateSelectedState();
    }

    protected void updateSelectedState() {
        final boolean prettySyntax =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        NotationInfo.DEFAULT_PRETTY_SYNTAX = prettySyntax;
        setSelected(prettySyntax);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        // Needs to be executed before the// ViewSettings are modified, because the UI
        // will react on the settings change event!
        NotationInfo.DEFAULT_PRETTY_SYNTAX = selected;
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(selected);
    }

    protected void updateMainWindow(boolean prettySyntax) {
        mainWindow.getUnicodeToggleAction().setEnabled(prettySyntax);
        mainWindow.getHidePackagePrefixToggleAction().setEnabled(prettySyntax);
        mainWindow.makePrettyView();
    }

    protected void handleViewSettingsChanged(PropertyChangeEvent e) {
        updateSelectedState();
        final boolean prettySyntax =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        updateMainWindow(prettySyntax);
    }
}
