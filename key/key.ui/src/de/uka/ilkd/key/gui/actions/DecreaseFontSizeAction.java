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

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;

public class DecreaseFontSizeAction extends MainWindowAction implements ConfigChangeListener {
    
    /**
     * generated sUID
     */
    private static final long serialVersionUID = 8774824535047619737L;

    /**
     * creates the action to decrease the font size of the sequent and proof view
     * @param mainWindow the main window
     */
    public DecreaseFontSizeAction(MainWindow mainWindow) {
	super(mainWindow);
	
	setName("Smaller");
        setIcon(IconFactory.minus(16));
		
        Config.DEFAULT.addConfigChangeListener(this);
    }
    
    @Override
    public void actionPerformed(ActionEvent e) {
        Config.DEFAULT.smaller();
    }

    @Override
    public void configChanged(ConfigChangeEvent e) {
        setEnabled(!Config.DEFAULT.isMinimumSize());
    }

}