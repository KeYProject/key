// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import javax.swing.*;
import javax.swing.border.TitledBorder;

public class SimultaneousUpdateSimplifierConfiguration extends JDialog {

    private SimultaneousUpdateSimplifierSettings settingsFromConfigurationFile;

    private KeYMediator mediator = null;

    private boolean localDeleteEffectlessUpdates = false;
    private boolean localEagerMode = false;


    /** creates a new HeuristicSelector */
    public SimultaneousUpdateSimplifierConfiguration
	(KeYMediator mediator, 
	 SimultaneousUpdateSimplifierSettings settings) {  
	super(new JFrame(), "Update Simplification", true);

	settingsFromConfigurationFile = settings;

	localDeleteEffectlessUpdates = deleteEffectlessUpdates();
	localEagerMode = eagerMode();

	setMediator(mediator);

	layoutSimutanUpdatesimplifier(); 
	
	pack();
	setLocation(70,70);
    }


    /** sets the mediator to correspond with other gui elements
     * @param mediator the KeYMediator
     */
    public void setMediator(KeYMediator mediator) {	
	this.mediator = mediator;
    }

    // setter

    private void setDeleteEffectlessUpdates(boolean b) {
	localDeleteEffectlessUpdates = b;
    }

    private void setEagerMode(boolean b) {
	localEagerMode = b;
    }

    private void pushSettings() {
	settingsFromConfigurationFile.setDeleteEffectlessUpdates(localDeleteEffectlessUpdates);
	settingsFromConfigurationFile.setEagerMode(localEagerMode);

	mediator.setSimplifier(settingsFromConfigurationFile.getSimplifier());
    }

    // getter


    public boolean deleteEffectlessUpdates() {
	return settingsFromConfigurationFile.deleteEffectlessUpdates();
    }

    public boolean eagerMode() {
	return settingsFromConfigurationFile.eagerMode();
    }


    /** lays out the configuration dialog */
    public void layoutSimutanUpdatesimplifier() {	
	JPanel checkBoxPanel = new JPanel(new GridLayout(2,1));
	checkBoxPanel.setBorder(new TitledBorder("Current Configuration"));

	
	JCheckBox delete_effectless_cb = new JCheckBox("Delete effectless updates",
						   deleteEffectlessUpdates()); 
	delete_effectless_cb.addItemListener( new ItemListener() {
		public void itemStateChanged(ItemEvent ce) {
		    setDeleteEffectlessUpdates(ce.getStateChange() == ItemEvent.SELECTED);
		}
	    });
	


	checkBoxPanel.add(delete_effectless_cb);


	JCheckBox eagerModeCheckbox = new JCheckBox("One Pass Simplification",
						    eagerMode()); 
	eagerModeCheckbox.addItemListener( new ItemListener() {
		public void itemStateChanged(ItemEvent ce) {
		    setEagerMode(ce.getStateChange() == ItemEvent.SELECTED);
		}
	    });
	


	checkBoxPanel.add(eagerModeCheckbox);


	
	JPanel buttonPanel = new JPanel(new GridLayout(1,2));
	JButton ok = new JButton("OK");
	ok.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
		    pushSettings();
		    dispose();
		}
	    });
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent ae) {
		    dispose();
		}
	    });
	buttonPanel.add(ok);
	buttonPanel.add(cancel);

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(checkBoxPanel, BorderLayout.CENTER);
	getContentPane().add(buttonPanel, BorderLayout.SOUTH);	
	
    }

    

}
