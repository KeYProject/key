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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;

import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class ModelSourceSelector extends JDialog {

    private ModelSourceSettings settings;
    private JRadioButton xmiFile;
    private JRadioButton tccModel;

    public ModelSourceSelector() {  
	super(new JFrame(), "Select UML Model Source", true);
	settings = ProofSettings.DEFAULT_SETTINGS.getModelSourceSettings();
	layoutModelSourceSelector();
	init(settings);

	pack();
	setLocation(70, 70);
	setVisible(true);
    }

    public ModelSourceSettings getSettings(){
	return settings;
    }

    /** layout */
    protected void layoutModelSourceSelector() {

	JButton ok = new JButton("OK");
	ok.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setVisible(false);
		    settings.store();
		    dispose();
		}
	    });
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setVisible(false);
		    settings.restore();
		    dispose();
		}
	    });
	xmiFile = new JRadioButton("XMI file");
	xmiFile.setActionCommand("xmi");
	tccModel = new JRadioButton("TogetherCC data structures");
	tccModel.setActionCommand("tcc");

	RadioListener listener = new RadioListener();
	xmiFile.addActionListener(listener);
	tccModel.addActionListener(listener);
	
	ButtonGroup group = new ButtonGroup();
	group.add(xmiFile);
	group.add(tccModel);

 	JPanel buttonPanel = new JPanel();
 	buttonPanel.add(ok);
 	buttonPanel.add(cancel);	

	JPanel listPanel=new JPanel();
	listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.Y_AXIS));
	listPanel.add(xmiFile);
	listPanel.add(tccModel);

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(new JPanel(),BorderLayout.WEST);
	getContentPane().add(listPanel,BorderLayout.CENTER);
	getContentPane().add(buttonPanel,BorderLayout.SOUTH);
    }

    private void init(ModelSourceSettings msSettings) {
	if ("0".equals(msSettings.getModelSource())){
	    xmiFile.setSelected(true);
	}
	else {
	    tccModel.setSelected(true);
	}
    }

    /** is called to set the chosen LDT */
    private void setModelSource(String sel) {
	settings.setModelSource(sel);	    
    }


    class RadioListener implements ActionListener {
	public void actionPerformed(ActionEvent e) {
	    if ("xmi".equals(e.getActionCommand()))
		setModelSource("0");
	    else 
		setModelSource("1");
	}
    }
    
   
}    
