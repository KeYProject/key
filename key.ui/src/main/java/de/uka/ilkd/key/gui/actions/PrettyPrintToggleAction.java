/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;


import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.util.EventObject;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class PrettyPrintToggleAction extends MainWindowAction {
    public static final String NAME = "Use Pretty Syntax";

    public static final String TOOL_TIP = "If ticked, infix notations are used.";

    /**
     *
     */
    private static final long serialVersionUID = 8633254204256247698L;

    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the
     * KeYIDE.
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
                .addPropertyChangeListener(viewSettingsListener);
        updateSelectedState();
    }

    protected void updateSelectedState() {
        final boolean prettySyntax =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        NotationInfo.DEFAULT_PRETTY_SYNTAX = prettySyntax;
        setSelected(prettySyntax);
        // setSelected(NotationInfo.PRETTY_SYNTAX);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        // Needs to be executed before the// ViewSettings are modified, because the UI
        // will react on the settings change event!
        NotationInfo.DEFAULT_PRETTY_SYNTAX = selected;
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(selected);
        updateMainWindow(selected);
    }

    protected void updateMainWindow(boolean prettySyntax) {
        mainWindow.getUnicodeToggleAction().setEnabled(prettySyntax);
        mainWindow.getHidePackagePrefixToggleAction().setEnabled(prettySyntax);
        mainWindow.makePrettyView();
    }

    protected void handleViewSettingsChanged(EventObject e) {
        updateSelectedState();
        final boolean prettySyntax =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        updateMainWindow(prettySyntax);
    }
}
