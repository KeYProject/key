// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

/*
 * Is this a legacy option?
 * Finding instantiations seems to be done by the prover, even if this
 * option is disabled.
 * (Kai Wallisch, December 2013)
 */
public class MinimizeInteraction extends KeYMenuCheckBox {

    private final MainWindow mainWindow;

    public MinimizeInteraction(MainWindow mainWindow) {
        super(mainWindow, "Minimize Interaction");
        this.mainWindow = mainWindow;
        setName("MinimizeInteractionInstance");
        setTooltip("If ticked and automated strategy (play button) is used, the prover tries to minimize user interaction, "
                + "e.g., if the prover can find instantiations by itself, it will not ask the user to provide them.");
    }

    @Override
    public void handleClickEvent() {
        boolean b = isSelected();
        mainWindow.getMediator().setMinimizeInteraction(b);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(b);
    }

}
