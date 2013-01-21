// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;

public class FileOpenNotification extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = 5271280688046955444L;
    private JCheckBox showAlwaysCB;

    /** 
     * creates a new FileOpenNotification
     * @param parent The parent widget of this FileOpenNotification 
     */
    public FileOpenNotification(JFrame parent) {  
	super(parent, "About opening source files", true);
	layoutFileOpenNotification(); 
	pack();
	setLocation(70,70);
    }

    protected void layoutFileOpenNotification() {
		boolean show = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour();
    	
    	getContentPane().setLayout(new BorderLayout());
	
	 	JPanel notificationPanel=new JPanel();
	 	notificationPanel.setLayout(new BoxLayout(notificationPanel, BoxLayout.X_AXIS));
	 	notificationPanel.add(new JLabel("<html><font color=\"#000000\">"
	 			+ "When loading a java source file, all java files<br>"
				+ " in the same directory or its parent will also be<br>"
				+ " loaded. </font></html>"));
		
		JPanel showAlwaysPanel = new JPanel();
	 	showAlwaysPanel.setLayout(new BoxLayout(showAlwaysPanel,
				BoxLayout.X_AXIS));
	 	showAlwaysCB = new JCheckBox("Always show this notification", show);
	 	showAlwaysPanel.add(showAlwaysCB);
	
	 	JButton okButton = new JButton("OK");
		okButton.setMnemonic(KeyEvent.VK_ENTER);
	
	 	okButton.addActionListener(new ActionListener() {
	 		public void actionPerformed(ActionEvent e) {
			    boolean ifind = showAlwaysCB.isSelected();
			    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setNotifyLoadBehaviour(ifind);
			    setVisible(false);
                            dispose();
	 		}
		    });
	 	JPanel buttonPanel = new JPanel();
	 	buttonPanel.add(okButton);
		
		getContentPane().setLayout(new BoxLayout(getContentPane(), 
							 BoxLayout.Y_AXIS));
		getContentPane().add(notificationPanel);
		getContentPane().add(showAlwaysPanel);
		getContentPane().add(buttonPanel);
    }
}