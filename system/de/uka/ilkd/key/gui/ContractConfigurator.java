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

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


public class ContractConfigurator extends JDialog {
    
    private OperationContractSelectionPanel contractPanel;
    private ClassInvariantSelectionPanel assumedInvPanel;
    private ClassInvariantSelectionPanel ensuredInvPanel;
    private JButton okButton;
    private JButton cancelButton;
    
    private boolean successful = false;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    /**
     * Helper for constructors.
     */
    private void init(Services services, 
                      ProgramMethod pm,
                      Modality modality,
                      boolean allowContract,
                      boolean allowAssumedInvs,
                      boolean allowEnsuredInvs) {
        assert allowContract || allowAssumedInvs || allowEnsuredInvs;
        
        JTabbedPane tabbedPane = new JTabbedPane();
        
        //create contract panel
        if(allowContract) {
            contractPanel = new OperationContractSelectionPanel(services, 
                                                                pm, 
                                                                modality);
            contractPanel.addMouseListener(new MouseAdapter() {
                public void mouseClicked(MouseEvent e){                
                    if(e.getClickCount() == 2){
                       okButton.doClick();
                    }
                }
            });
            tabbedPane.addTab("Contract", contractPanel);
        }
        
        //create assumed inv panel
        if(allowAssumedInvs) {
            assumedInvPanel 
                    = new ClassInvariantSelectionPanel(services, 
                                                       false, 
                                                       pm.getContainerType(), 
                                                       true);
            tabbedPane.addTab("Assumed Invariants", assumedInvPanel);
        }
        
        //create ensured inv panel
        if(allowEnsuredInvs) {
            ensuredInvPanel
                    = new ClassInvariantSelectionPanel(services, 
                                                       false, 
                                                       pm.getContainerType(), 
                                                       true);
            tabbedPane.addTab("Ensured Invariants", ensuredInvPanel);
        }
        tabbedPane.setMinimumSize(new Dimension(800, 500));
        getContentPane().add(tabbedPane);
        
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
                            JButton.WHEN_IN_FOCUSED_WINDOW);

        
        //show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));        
        pack();
        setLocation(70, 70);        
        setVisible(true);
    }
      
    
    public ContractConfigurator(JDialog owner,
            Services services, 
            ProgramMethod pm,
            Modality modality,
            boolean allowContract,
            boolean allowAssumedInvs,
            boolean allowEnsuredInvs) {
        super(owner, "Contract Configurator", true);
	init(services, 
             pm, 
             modality, 
             allowContract, 
             allowAssumedInvs, 
             allowEnsuredInvs);
    }
    
    
    public ContractConfigurator(Frame owner,
                                Services services,
                                ProgramMethod pm,
                                Modality modality,
                                boolean allowContract,
                                boolean allowAssumedInvs,
                                boolean allowEnsuredInvs) {
        super(owner, "Contract Configurator", true);
        init(services, 
             pm, 
             modality, 
             allowContract, 
             allowAssumedInvs, 
             allowEnsuredInvs);
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
    public OperationContract getContract() {
	return contractPanel.getOperationContract();
    }
    
    
    /**
     * Returns the selected set of assumed invariants.
     */
    public SetOfClassInvariant getAssumedInvs() {
	return assumedInvPanel.getClassInvariants();
    }

    
    /**
     * Returns the selected set of ensured invariants.
     */
    public SetOfClassInvariant getEnsuredInvs() {
	return ensuredInvPanel.getClassInvariants();
    }
    
    
    /**
     * Returns the selected tuple (contract, assumed invs, ensured invs).
     */
    public ContractWithInvs getContractWithInvs() {
        return new ContractWithInvs(getContract(), 
                                    getAssumedInvs(), 
                                    getEnsuredInvs());
    }
}
