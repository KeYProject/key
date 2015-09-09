// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class SyntaxHighlightingToggleAction extends MainWindowAction {
    private static final long serialVersionUID = 6987252955535709994L;

    public SyntaxHighlightingToggleAction(MainWindow window) {
        super(window);
        setName("Use syntax highlighting");
        setTooltip("Uses regular expressions-based syntax highlighting. "
                + "This helps to understand sequents, but may "
                + "slow down the rendering of longer ones.");
        final boolean useSyntaxHighlighting =
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                        .isUseSyntaxHighlighting();
        setSelected(useSyntaxHighlighting);
        NotationInfo.DEFAULT_SYNTAX_HIGHLIGHTING_ENABLED =
                useSyntaxHighlighting;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean useSyntaxHighlighting = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setUseSyntaxHighlighting(useSyntaxHighlighting);
        mainWindow.makePrettyView();
    }

}