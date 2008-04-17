// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
    	int maxLinesInt = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
				.getMaxTooltipLines();
		boolean showWholeTaclet = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
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
			    int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
			    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setMaxTooltipLines(maxSteps);
			    boolean ifind = showWholeTacletCB.isSelected();
			    ProofSettings.DEFAULT_SETTINGS.getViewSettings().setShowWholeTaclet(ifind);
			    
			    setVisible(false);
	 		}
		    });
	 	JButton saveButton = new JButton("Save as Default");
	
	 	saveButton.addActionListener(new ActionListener() {
	 		public void actionPerformed(ActionEvent e) {
			    int maxSteps = 
	                        Integer.parseInt(maxTooltipLinesInputField.getText());
			    ProofSettings dflt=ProofSettings.DEFAULT_SETTINGS;
			    boolean ifind = showWholeTacletCB.isSelected();
			    dflt.getViewSettings().setMaxTooltipLines(maxSteps);
			    dflt.getViewSettings().setShowWholeTaclet(ifind);
			    //temporary solution, stores more than wanted %%%% 
			    dflt.saveSettings();
			    setVisible(false);
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

	public void insertString(int offs, String str, AttributeSet a) 
	    throws BadLocationException {
	    if (str == null) {
		return;
	    }
	    char[] upper = str.toCharArray();
	    for (int i = 0; i < upper.length; i++) {
		if (upper[i] < '0' || upper[i] > '9') {
		    return;
		} 
	    }
	    super.insertString(offs, new String(upper), a);
	}
	
    }

    static class NumberInputField extends JTextField {
	public NumberInputField(int number, int cols) {
	    super(cols);
	    setText(""+number);
	}

	protected Document createDefaultModel() {
	    return new NumberDocument();
	}
    }



}    
