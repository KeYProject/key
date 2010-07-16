// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.speclang.OperationContract;


public class UsedSpecificationsDialog extends JDialog {
    
    private static final ImageIcon keyIcon 
        = IconFactory.keyHole(20, 20);
    private static final ImageIcon keyAlmostClosedIcon 
        = IconFactory.keyHoleAlmostClosed(20, 20);
    private static final ImageIcon keyClosedIcon
        = IconFactory.keyHoleClosed(20, 20);
    
    private final Services services;
    private final JList contractAppList;
    private final JButton ensuresPostButton;
    private final JButton preservesInvButton;
    private final JButton respectsModifiesButton;
    private final JButton cancelButton;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public UsedSpecificationsDialog(Services services, 
                                    ImmutableSet<ContractWithInvs> contractApps) {
        super(Main.getInstance(), "Used Specifications", true);
        this.services = services;
        
        //break contract apps down to atomic contracts
        ImmutableSet<ContractWithInvs> atomicContractApps 
            = DefaultImmutableSet.<ContractWithInvs>nil();
        for(ContractWithInvs cwi : contractApps) {
            for(OperationContract atomicContract 
                : services.getSpecificationRepository()
                          .splitContract(cwi.contract)) {
                ContractWithInvs atomicCwi 
                    = new ContractWithInvs(atomicContract, 
                                           cwi.assumedInvs, 
                                           cwi.ensuredInvs);
                atomicContractApps = atomicContractApps.add(atomicCwi);
            }
        }
                
        //create scroll pane
        JScrollPane scrollPane = new JScrollPane();
        Dimension scrollPaneDim = new Dimension(800, 500);
        scrollPane.setPreferredSize(scrollPaneDim);
        scrollPane.setMinimumSize(scrollPaneDim);
        getContentPane().add(scrollPane);
        
        //create contract app list
        contractAppList = new JList();
        contractAppList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        contractAppList.setListData(atomicContractApps.toArray(new ContractWithInvs[atomicContractApps.size()]));
        contractAppList.setSelectedIndex(0);
        contractAppList.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {                
                if(contractAppList.isSelectionEmpty()) {
                    contractAppList.setSelectedIndex(e.getFirstIndex());
                }
                updatePOButtons();
            }
        });
        contractAppList.setCellRenderer(new DefaultListCellRenderer() {
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);
            
            public Component getListCellRendererComponent(
                                                    JList list,
                                                    Object value,
                                                    int index,
                                                    boolean isSelected,
                                                    boolean cellHasFocus) {
                ContractWithInvs cwi = (ContractWithInvs) value;
                Component supComp 
                        = super.getListCellRendererComponent(list, 
                                                             value, 
                                                             index, 
                                                             isSelected, 
                                                             cellHasFocus);             
                
                //create label and enclosing panel
                JLabel label = new JLabel();
                label.setText(cwi.getHTMLText(
                            UsedSpecificationsDialog.this.services));
                label.setFont(PLAINFONT);
                FlowLayout lay = new FlowLayout();
                lay.setAlignment(FlowLayout.LEFT);
                JPanel result = new JPanel(lay);
                result.add(label);
                label.setVerticalAlignment(SwingConstants.TOP);
                
                //set background color
                result.setBackground(supComp.getBackground());

                //set border
                TitledBorder border = new TitledBorder(
                                BorderFactory.createEtchedBorder(),
                                cwi.contract.getDisplayName());
                border.setTitleFont(border.getTitleFont()
                                          .deriveFont(Font.BOLD));
                result.setBorder(border);
                
                return result;
            }
        });
        scrollPane.setViewportView(contractAppList);
                        
        //create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(115, 27);
        Dimension largeButtonDim = new Dimension(145, 27);
        Dimension extraLargeButtonDim = new Dimension(170, 27);
        getContentPane().add(buttonPanel);
        
        
        final DefaultPOProvider poProvider = (services.getProof() != null ? 
        	services.getProof().getSettings().getProfile() : ProofSettings.DEFAULT_SETTINGS.getProfile()).getPOProvider();
        
        //create "EnsuresPost" button
        ensuresPostButton = new JButton("EnsuresPost");
        ensuresPostButton.setPreferredSize(largeButtonDim);
        ensuresPostButton.setMinimumSize(largeButtonDim);
        ensuresPostButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                ContractWithInvs cwi 
                    = (ContractWithInvs) contractAppList.getSelectedValue();
                InitConfig initConfig = Main.getInstance().mediator()
                                                          .getSelectedProof()
                                                          .env()
                                                          .getInitConfig();
                ProofOblInput po = poProvider.createEnsuresPostPO(initConfig, 
                                                     cwi.contract, 
                                                     cwi.assumedInvs);
                findOrStartProof(initConfig, po);
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(ensuresPostButton);
        
        //create "PreservesInv" button
        preservesInvButton = new JButton("PreservesInv");
        preservesInvButton.setPreferredSize(largeButtonDim);
        preservesInvButton.setMinimumSize(largeButtonDim);
        preservesInvButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                ContractWithInvs cwi 
                    = (ContractWithInvs) contractAppList.getSelectedValue();
                InitConfig initConfig = Main.getInstance().mediator()
                                                          .getSelectedProof()
                                                          .env()
                                                          .getInitConfig();
                ProofOblInput po 
                    = poProvider.createPreservesInvPO(initConfig, 
                                         cwi.contract.getProgramMethod(),
                                         cwi.assumedInvs,
                                         cwi.ensuredInvs);
                findOrStartProof(initConfig, po);
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(preservesInvButton);
        
        //create "RespectsModifies" button
        respectsModifiesButton = new JButton("RespectsModifies");
        respectsModifiesButton.setPreferredSize(extraLargeButtonDim);
        respectsModifiesButton.setMinimumSize(extraLargeButtonDim);
        respectsModifiesButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                ContractWithInvs cwi 
                    = (ContractWithInvs) contractAppList.getSelectedValue();
                InitConfig initConfig = Main.getInstance().mediator()
                                                          .getSelectedProof()
                                                          .env()
                                                          .getInitConfig();
                ProofOblInput po
                    = poProvider.createRespectsModifiesPO(initConfig, 
                                             cwi.contract, 
                                             cwi.assumedInvs);
                findOrStartProof(initConfig, po);
                setVisible(false);
            }
        });
        buttonPanel.add(respectsModifiesButton);
        
        //create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        });
        buttonPanel.add(cancelButton);
        getRootPane().setDefaultButton(cancelButton);
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
        
        //disable PO buttons if no specifications
        if(atomicContractApps.size() == 0) {
            ensuresPostButton.setEnabled(false);
            preservesInvButton.setEnabled(false);
            respectsModifiesButton.setEnabled(false);
        } else {
            updatePOButtons();
        }
        
        //show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS)); 
        pack();
        setLocation(70, 70);
        setVisible(true);        
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Proof findPreferablyClosedProof(ProofOblInput po) {
        ImmutableSet<Proof> proofs 
            = services.getSpecificationRepository().getProofs(po);
        
        //no proofs?
        if(proofs.size() == 0) {
            return null;
        }
        
        //try to find closed proof
        for (final Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }
        
        //just take any proof
        return proofs.iterator().next();
    }
    
    
    private void updatePOButtons() {
        InitConfig initConfig = Main.getInstance().mediator()
                                                  .getSelectedProof()
                                                  .env()
                                                  .getInitConfig();
        
        DefaultPOProvider poProvider = initConfig.getProfile().getPOProvider();
        
        ContractWithInvs cwi 
            = (ContractWithInvs) contractAppList.getSelectedValue();
        
        //ensuresPost
        ProofOblInput ensuresPostPO = poProvider.createEnsuresPostPO(initConfig, 
                                                        cwi.contract, 
                                                        cwi.assumedInvs);
        Proof ensuresPostProof = findPreferablyClosedProof(ensuresPostPO);
        if(ensuresPostProof == null) {
            ensuresPostButton.setIcon(null);
        } else if(ensuresPostProof.mgt().getStatus().getProofOpen()) {
            ensuresPostButton.setIcon(keyIcon);
        } else if(ensuresPostProof.mgt().getStatus()
                                        .getProofClosedButLemmasLeft()) {
            ensuresPostButton.setIcon(keyAlmostClosedIcon);
        } else {
            assert ensuresPostProof.mgt().getStatus().getProofClosed();
            ensuresPostButton.setIcon(keyClosedIcon);
        }

        //preservesInv
        ProofOblInput preservesInvPO 
            = poProvider.createPreservesInvPO(initConfig, 
                                 cwi.contract.getProgramMethod(), 
                                 cwi.assumedInvs,
                                 cwi.ensuredInvs);
        Proof preservesInvProof = findPreferablyClosedProof(preservesInvPO);
        if(preservesInvProof == null) {
            preservesInvButton.setIcon(null);
        } else if(preservesInvProof.mgt().getStatus().getProofOpen()) {
            preservesInvButton.setIcon(keyIcon);
        } else if(preservesInvProof.mgt().getStatus()
                                        .getProofClosedButLemmasLeft()) {
            preservesInvButton.setIcon(keyAlmostClosedIcon);
        } else {
            assert preservesInvProof.mgt().getStatus().getProofClosed();
            preservesInvButton.setIcon(keyClosedIcon);
        }
        
        //respectsModifies
        ProofOblInput respectsModifiesPO 
            = poProvider.createRespectsModifiesPO(initConfig, 
                                     cwi.contract, 
                                     cwi.assumedInvs);
        Proof respectsModifiesProof = findPreferablyClosedProof(respectsModifiesPO);
        if(respectsModifiesProof == null) {
            respectsModifiesButton.setIcon(null);
        } else if(respectsModifiesProof.mgt().getStatus().getProofOpen()) {
            respectsModifiesButton.setIcon(keyIcon);
        } else if(respectsModifiesProof.mgt().getStatus()
                                        .getProofClosedButLemmasLeft()) {
            respectsModifiesButton.setIcon(keyAlmostClosedIcon);
        } else {
            assert respectsModifiesProof.mgt().getStatus().getProofClosed();
            respectsModifiesButton.setIcon(keyClosedIcon);
        }
    }
    
    
    private void findOrStartProof(InitConfig initConfig, ProofOblInput po) {
        Proof proof = findPreferablyClosedProof(po);
        if(proof == null) {
            ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
            try {
                pi.startProver(initConfig, po);
            } catch(ProofInputException exc) {
                exc.printStackTrace(System.out);
            }
        } else {
            Main.getInstance().mediator().setProof(proof);
        }
    }
}
