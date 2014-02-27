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


/** common superclass of TacletIfSelectionDialog and TacletMatchCompletionDialog */
package de.uka.ilkd.key.gui;


import java.awt.*;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.StringWriter;
import java.io.Writer;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.pp.StringBackend;


public abstract class ApplyTacletDialog extends JDialog {


    /**
     * 
     */
    private static final long serialVersionUID = -411398660828882035L;
    // buttons
    protected JButton cancelButton;
    protected JButton applyButton;
   
    private KeYMediator mediator;
    protected boolean checkAfterEachInput=true;

    protected ApplyTacletDialogModel[] model; 
    private JTextArea statusArea;

    public ApplyTacletDialog(Frame parent, ApplyTacletDialogModel[] model,
			     KeYMediator mediator) { 

        super(parent, "Choose Taclet Instantiation", false);
//	setSize(800,700);
//	setLocation(70,50);

	this.mediator = mediator;
	this.model = model;

	applyButton  = new JButton("Apply");
	cancelButton = new JButton("Cancel");
    
	mediator.requestModalAccess(this); 
	addWindowListener(new WindowAdapter() {
                @Override
		public void windowClosed(WindowEvent e) {
		    ApplyTacletDialog.this.closeDlg();		    
		}

                @Override
		public void windowClosing(WindowEvent e) {
		    ApplyTacletDialog.this.closeDlg();
		}
	    });
    }
    
    protected KeYMediator mediator() {
    	return mediator;
    }

    private int countLines(String s) {
		int i=0;
		int p=0;
		while ((p=s.indexOf("\n",p))>=0) {
			i++;
			p++;
		}
		return i+1;
    }
    
    protected JPanel createInfoPanel() {
	ImmutableList<Named> vars=model[0].programVariables().elements();
	JPanel panel = new JPanel(new GridLayout(1,1));
	panel.setBorder(new TitledBorder("Sequent program variables"));       
	JScrollPane scroll = new JScrollPane();
	JTextArea text;
	if (vars.size()>0) {
	    text = new JTextArea(vars.toString(),2,40);
	} else {
	    text = new JTextArea("none",1,40);
	}
	scroll.setViewportView(text);
	text.setEditable(false);
	panel.add(scroll, BorderLayout.CENTER);
	return panel;
    }

    protected JPanel createTacletDisplay()  {
        JPanel panel = new JPanel(new BorderLayout());	
        panel.setBorder
        (new TitledBorder("Selected Taclet - "+model[0].taclet().name()));
        Debug.log4jDebug("TacletApp: "+model[0].taclet(), ApplyTacletDialog.class.getName());
        
        Taclet taclet = model[0].taclet();
        StringBackend backend = new StringBackend(68);
        StringBuilder tacletSB = new StringBuilder();
        
        Writer w = new StringWriter();
        //WriterBackend backend = new WriterBackend(w, 68);
        
        SequentViewLogicPrinter tp = new SequentViewLogicPrinter(new ProgramPrinter(w), 
                new NotationInfo(), backend, mediator.getServices(), true,
                MainWindow.getInstance().getVisibleTermLabels());
        
//        tp.printTaclet(taclet, model[0].tacletApp().instantiations(),
        tp.printTaclet(taclet, 
        	       SVInstantiations.EMPTY_SVINSTANTIATIONS,
        	       ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(), 
//        	       ProofSettings.DEFAULT_SETTINGS.getViewSettings().getShowWholeTaclet(), 
        	       false);
        tacletSB.append(backend.getString());
        
        //logger.info(tacletSB);
        //System.out.println(tacletSB);
        
        panel.setAlignmentY(Component.TOP_ALIGNMENT);
        // show taclet
        JScrollPane scroll = new JScrollPane();
        int nolines=countLines(model[0].taclet().toString())+1;
        if (nolines>10) nolines=11;
        //JTextArea text=new JTextArea(model[0].taclet().toString(),nolines,40);
        JTextArea text=new JTextArea(tacletSB.toString(), nolines, 68);
        text.setEditable(false);
        scroll.setViewportView(text);
        panel.add(scroll, BorderLayout.CENTER);
        
        return panel;
    }

    protected abstract void pushAllInputToModel();
    protected abstract int current();

    public boolean checkAfterEachInput() {
    	return checkAfterEachInput;
    }

    protected JPanel createStatusPanel() {
        JPanel statusPanel = new JPanel(new BorderLayout());

        statusArea = new JTextArea();
	statusArea.setEditable(false);

        statusPanel.add(
                new JScrollPane(statusArea,
                        ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED),
                BorderLayout.CENTER);
        statusPanel.setBorder(new TitledBorder("Input validation result"));
        setStatus(model[current()].getStatusString());
        return statusPanel;
    }

    protected JPanel createButtonPanel(ActionListener buttonListener) {
	JPanel panel=new JPanel(new GridBagLayout());
	GridBagConstraints c = new GridBagConstraints();

	cancelButton.addActionListener(buttonListener);
	applyButton.addActionListener(buttonListener);
	c.insets = new Insets(5,20,5,20);
	c.gridx = 0;
	panel.add(cancelButton, c);    

	c.gridx = 1;
	panel.add(applyButton, c);    
	panel.setAlignmentY(Component.BOTTOM_ALIGNMENT);

	return panel;
    }

    protected void setStatus(String s) {
	if (statusArea != null) {
	    statusArea.setText(s); 
	}
    }

    protected void closeDlg() {
	mediator.freeModalAccess(this);
    }
}
