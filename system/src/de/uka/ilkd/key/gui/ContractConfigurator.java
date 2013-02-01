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


package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.event.*;

import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;


public class ContractConfigurator extends JDialog {
    
    /**
     * 
     */
    private static final long serialVersionUID = 4002043118399402599L;
    private ContractSelectionPanel contractPanel;
    private JButton okButton;
    private JButton cancelButton;
    
    private boolean successful = false;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public ContractConfigurator(JDialog owner,
            		        Services services, 
            		        Contract[] contracts,
            		        String title,
            		        boolean allowMultipleContracts) {
        super(owner, "Contract Configurator", true);
        init(services,
             contracts,
             title,
             allowMultipleContracts);
    }
    
    
    public ContractConfigurator(Frame owner,
                                Services services,
                                Contract[] contracts,
                                String title,
                                boolean allowMultipleContracts) {
        super(owner, "Contract Configurator", true);
        init(services,
             contracts,
             title,
             allowMultipleContracts);
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Helper for constructors.
     */
    private void init(Services services, 
                      Contract[] contracts,
                      String title,
                      boolean allowMultipleContracts) {        
        //create contract panel
        contractPanel = new ContractSelectionPanel(services, 
        				           allowMultipleContracts);
        contractPanel.setContracts(contracts, title);
        contractPanel.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e){                
        	if(e.getClickCount() == 2){
        	    okButton.doClick();
        	}
            }
        });        
        contractPanel.setMinimumSize(new Dimension(800, 500));
        getContentPane().add(contractPanel);
        
        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(100, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, 
                                                 (int)buttonDim.getHeight() 
                                                    + 10));
        getContentPane().add(buttonPanel);
        
        //create "ok" button
        okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = true;
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        //create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                successful = false;
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if(event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
                            escapeListener,
                            "ESC",
                            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                            JComponent.WHEN_IN_FOCUSED_WINDOW);

        
        //show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));        
        pack();
        setLocation(70, 70);        
        setVisible(true);
    }
      
    
   
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }


    /**
     * Returns the selected contract.
     */
    public Contract getContract() {
	return contractPanel.getContract();
    }
}
