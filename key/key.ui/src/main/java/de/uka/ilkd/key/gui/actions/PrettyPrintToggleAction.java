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
import java.util.EventObject;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

public class PrettyPrintToggleAction extends MainWindowAction {
    public static final String NAME = "Use pretty syntax";
    
    public static final String TOOL_TIP = "If ticked, infix notations are used.";
    
    /**
     * 
     */
    private static final long serialVersionUID = 8633254204256247698L;
    
    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the KeYIDE.
     */
    private final SettingsListener viewSettingsListener = new SettingsListener() {
       @Override
       public void settingsChanged(EventObject e) {
          handleViewSettingsChanged(e);
       }
    };

    public PrettyPrintToggleAction(MainWindow mainWindow) {
       super(mainWindow);
       setName(NAME);
       setTooltip(TOOL_TIP);
       ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().addSettingsListener(viewSettingsListener); // Attention: The listener is never removed, because there is only one MainWindow!
       updateSelectedState();
    }
    
    protected void updateSelectedState() {
       final boolean prettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
       NotationInfo.DEFAULT_PRETTY_SYNTAX = prettySyntax;
       setSelected(prettySyntax);
       //setSelected(NotationInfo.PRETTY_SYNTAX);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        NotationInfo.DEFAULT_PRETTY_SYNTAX = selected; // Needs to be executed before the ViewSettings are modified, because the UI will react on the settings change event!
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
       final boolean prettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
       updateMainWindow(prettySyntax);
    }
}