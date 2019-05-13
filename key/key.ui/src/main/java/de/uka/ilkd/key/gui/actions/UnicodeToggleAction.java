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
import de.uka.ilkd.key.util.UnicodeHelper;

@SuppressWarnings("serial")
public class UnicodeToggleAction extends MainWindowAction {
   public static final String NAME = "Use Unicode symbols";
   
   public static final String TOOL_TIP = "If checked formulae are displayed with special Unicode characters" +
                                         " (such as \""+UnicodeHelper.AND+"\") instead of the traditional ASCII ones. \n"+
                                         "Only works in combination with pretty printing (see above).";
   
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

    public UnicodeToggleAction(MainWindow window) {
        super(window);
        setName(NAME);
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().addSettingsListener(viewSettingsListener); // Attention: The listener is never removed, because there is only one MainWindow!
        updateSelectedState();
    }
    
    protected void updateSelectedState() {
       final boolean useUnicode = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
       final boolean usePretty = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
       setSelected((useUnicode && usePretty));
       NotationInfo.DEFAULT_UNICODE_ENABLED = (useUnicode && usePretty);
       setEnabled(usePretty);
       //setSelected(NotationInfo.UNICODE_ENABLED);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
       boolean useUnicode = ((JCheckBoxMenuItem) e.getSource()).isSelected(); 
       boolean usePretty = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
       NotationInfo.DEFAULT_UNICODE_ENABLED = useUnicode && usePretty; // Needs to be executed before the ViewSettings are modified, because the UI will react on the settings change event!
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