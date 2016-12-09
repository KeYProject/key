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

import java.util.EventObject;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

/*
 * Is this a legacy option?
 * Finding instantiations seems to be done by the prover, even if this
 * option is disabled.
 * (Kai Wallisch, December 2013)
 */
public class MinimizeInteraction extends KeYMenuCheckBox {
    public static final String NAME = "Minimize Interaction";
    public static final String TOOL_TIP = "If ticked and automated strategy (play button) is used, the prover tries to minimize user interaction, "
                                          + "e.g., if the prover can find instantiations by itself, it will not ask the user to provide them.";

    /**
     *
     */
    private static final long serialVersionUID = -3381517803006651928L;
    private final MainWindow mainWindow;
    
    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the KeYIDE.
     */
    private final SettingsListener generalSettingsListener = new SettingsListener() {
       @Override
       public void settingsChanged(EventObject e) {
          handleGeneralSettingsChanged(e);
       }
    };

    public MinimizeInteraction(MainWindow mainWindow) {
        super(mainWindow, NAME);
        this.mainWindow = mainWindow;
        setName("MinimizeInteractionInstance");
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().addSettingsListener(generalSettingsListener); // Attention: The listener is never removed, because there is only one MainWindow!
        updateSelectedState();
    }
    
    protected void updateSelectedState() {
       setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter());
    }

    @Override
    public void handleClickEvent() {
        boolean tacletFilter = isSelected();
        updateMainWindow(tacletFilter);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(tacletFilter);
    }
    
    protected void updateMainWindow(boolean b) {
       mainWindow.getUserInterface().getProofControl().setMinimizeInteraction(b);
    }

    protected void handleGeneralSettingsChanged(EventObject e) {
       updateSelectedState();
       final boolean tacletFilter = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter();
       updateMainWindow(tacletFilter);
    }
}