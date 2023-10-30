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
import de.uka.ilkd.key.util.UnicodeHelper;

public class UnicodeToggleAction extends MainWindowAction {
    private static final long serialVersionUID = 6078839876754730405L;

    public static final String NAME = "Use Unicode Symbols";

    public static final String TOOL_TIP =
        "If checked formulae are displayed with special Unicode characters" + " (such as \""
            + UnicodeHelper.AND + "\") instead of the traditional ASCII ones. \n"
            + "Only works in combination with pretty printing (see above).";

    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the
     * KeYIDE.
     */
    private final PropertyChangeListener viewSettingsListener = this::handleViewSettingsChanged;

    public UnicodeToggleAction(MainWindow window) {
        super(window);
        setName(NAME);
        setTooltip(TOOL_TIP);
        // Attention: The listener is never// removed, because there is only one
        // MainWindow!
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(viewSettingsListener);
        updateSelectedState();
    }

    protected void updateSelectedState() {
        final boolean useUnicode =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
        final boolean usePretty =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        setSelected((useUnicode && usePretty));
        NotationInfo.DEFAULT_UNICODE_ENABLED = (useUnicode && usePretty);
        setEnabled(usePretty);
        // setSelected(NotationInfo.UNICODE_ENABLED);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean useUnicode = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        boolean usePretty =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        NotationInfo.DEFAULT_UNICODE_ENABLED = useUnicode && usePretty; // Needs to be executed
                                                                        // before the ViewSettings
                                                                        // are modified, because the
                                                                        // UI will react on the
                                                                        // settings change event!
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(useUnicode);
        updateMainWindow();
    }

    protected void updateMainWindow() {
        mainWindow.makePrettyView();
    }

    protected void handleViewSettingsChanged(EventObject e) {
        updateSelectedState();
        updateMainWindow();
    }
}
