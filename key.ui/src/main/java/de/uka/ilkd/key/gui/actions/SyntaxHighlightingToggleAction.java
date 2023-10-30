/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class SyntaxHighlightingToggleAction extends MainWindowAction {
    private static final long serialVersionUID = 6987252955535709994L;

    public SyntaxHighlightingToggleAction(MainWindow window) {
        super(window);
        setName("Use Syntax Highlighting");
        setTooltip("Uses regular expressions-based syntax highlighting. "
            + "This helps to understand sequents, but may "
            + "slow down the rendering of longer ones.");
        final boolean useSyntaxHighlighting =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseSyntaxHighlighting();
        setSelected(useSyntaxHighlighting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean useSyntaxHighlighting = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setUseSyntaxHighlighting(useSyntaxHighlighting);
        mainWindow.makePrettyView();
    }

}
