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

package de.uka.ilkd.key.gui.configuration;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.*;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;
import javax.swing.text.PlainDocument;


public class ViewSelector extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = 5271280688046955444L;
    private JTextField maxTooltipLinesInputField;
    private JCheckBox showWholeTacletCB;

    /** 
     * creates a new ViewSelector
     * @param parent The parent widget of this ViewSelector 
     */
    public ViewSelector(JFrame parent) {  
	super(parent, "Maximum line number for tooltips", true);
	layoutViewSelector(); 
	pack();
	setLocation(70,70);
    }


    private void updateButtons() {

    }


    /** lays out the selector */
    protected void layoutViewSelector() {
//    	int maxLinesInt = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
//				.getMaxTooltipLines();
//		boolean showWholeTaclet = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
//				.getShowWholeTaclet();
    	int maxLinesInt = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
				.getMaxTooltipLines();
		boolean showWholeTaclet = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
				.getShowWholeTaclet();
    	
    	getContentPane().setLayout(new BorderLayout());
	
	 	JPanel maxLinesPanel=new JPanel();
	 	maxLinesPanel.setLayout(new BoxLayout(maxLinesPanel, BoxLayout.X_AXIS));
	 	maxTooltipLinesInputField = new NumberInputField(maxLinesInt, 4);
		maxTooltipLinesInputField.setMaximumSize(new Dimension(40,30));
	 	maxLinesPanel.add(new JLabel("<html><font color=\"#000000\">"
	 			+ "Maximum size (line count) of the tooltips of applicable rules"
				+ "<br> with schema variable instantiations displayed. "
				+ "In case of longer <br>tooltips the instantiation will be "
				+ "suppressed. </font></html>"));
		maxLinesPanel.add(maxTooltipLinesInputField);
		
		JPanel showWholeTacletPanel = new JPanel();
	 	showWholeTacletPanel.setLayout(new BoxLayout(showWholeTacletPanel,
				BoxLayout.X_AXIS));
	 	showWholeTacletCB = new JCheckBox("pretty-print whole Taclet including "
				+ "'name', 'find', 'varCond' and 'heuristics'", showWholeTaclet);
	 	showWholeTacletPanel.add(showWholeTacletCB);
	
	 	JButton okButton = new JButton("OK");
		okButton.setMnemonic(KeyEvent.VK_ENTER);
	
	 	okButton.addActionListener(new ActionListener() {
	 		public void actionPerformed(ActionEvent e) {
//			    int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
//			    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setMaxTooltipLines(maxSteps);
//			    boolean ifind = showWholeTacletCB.isSelected();
//			    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setShowWholeTaclet(ifind);
			    int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
			    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setMaxTooltipLines(maxSteps);
			    boolean ifind = showWholeTacletCB.isSelected();
			    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setShowWholeTaclet(ifind);
			    setVisible(false);
                            dispose();
	 		}
		    });
	 	JButton saveButton = new JButton("Save as Default");
	
	 	saveButton.addActionListener(new ActionListener() {
	 		public void actionPerformed(ActionEvent e) {
			    int maxSteps = 
	                        Integer.parseInt(maxTooltipLinesInputField.getText());
//			    ProofSettings dflt=ProofSettings.DEFAULT_SETTINGS;
			    ProofIndependentSettings dflt=ProofIndependentSettings.DEFAULT_INSTANCE;
			    boolean ifind = showWholeTacletCB.isSelected();
			    dflt.getViewSettings().setMaxTooltipLines(maxSteps);
			    dflt.getViewSettings().setShowWholeTaclet(ifind);
			    //temporary solution, stores more than wanted %%%% 
			    dflt.saveSettings();
			    setVisible(false);
                            dispose();
	 		}
		    });
	 	JButton cancelButton = new JButton("Cancel");
		cancelButton.setMnemonic(KeyEvent.VK_ESCAPE);
	 	cancelButton.addActionListener(new ActionListener() {
	 		public void actionPerformed(ActionEvent e) {
			    setVisible(false);
			    dispose();
	 		}
	 	    });
	
	 	JPanel buttonPanel = new JPanel();
	 	buttonPanel.add(okButton);
	 	buttonPanel.add(saveButton);
	 	buttonPanel.add(cancelButton);
		
		getContentPane().setLayout(new BoxLayout(getContentPane(), 
							 BoxLayout.Y_AXIS));
		getContentPane().add(maxLinesPanel);
		getContentPane().add(showWholeTacletPanel);
		getContentPane().add(buttonPanel);
	
		updateButtons();
	
    }
    
    

    // INNER CLASS TO READ ONLY NUMBERS FOR MAX APPs
    static class NumberDocument extends PlainDocument {

	/**
         * 
         */
        private static final long serialVersionUID = -5423315366275141764L;

    public void insertString(int offs, String str, AttributeSet a) 
	    throws BadLocationException {
	    if (str == null) {
		return;
	    }
	    char[] upper = str.toCharArray();
        for (char anUpper : upper) {
            if (anUpper < '0' || anUpper > '9') {
                return;
            }
        }
	    super.insertString(offs, new String(upper), a);
	}
	
    }

    static class NumberInputField extends JTextField {
	/**
         * 
         */
        private static final long serialVersionUID = 5578481785681533620L;

    public NumberInputField(int number, int cols) {
	    super(cols);
	    setText(""+number);
	}

	protected Document createDefaultModel() {
	    return new NumberDocument();
	}
    }



}