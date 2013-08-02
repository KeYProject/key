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

package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.lemmatagenerator.ItemChooser.ItemFilter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;
/**
 * The core of the Selection-Dialog is the class SelectionPanel which extends JPanel.
 * It contains a table for presenting the taclets using special filters. 
 * The dialog owns two SelectionPanels, one for presenting the taclets that can be chosen by the user (),
 * and one for presenting the taclets that the user has chosen. Both tables work on the 
 * same model but using different filters: 
 * A taclet is wrapped by an object of type TableItem which contains the taclet itself and 
 * a additional information about on which side it should be shown (LEFT or RIGHT). 
 * The taclet
 * 
 */




public class LemmaSelectionDialog extends JDialog implements TacletFilter {

        private static final long serialVersionUID = 1L;

        private JButton okayButton;
        private JCheckBox showSupported;
        private JButton cancelButton;
        private JPanel buttonPanel;
        private JPanel contentPanel;
        private ItemChooser<TacletInfo> tacletChooser;
        private ItemFilter<TacletInfo> showOnlySupportedTaclets = new ItemFilter<TacletInfo>(){

                @Override
                public boolean include(TacletInfo itemData) {
                       return !itemData.isNotSupported();
                }                
        };
        
        private ItemFilter<TacletInfo> filterForMovingTaclets = new ItemFilter<TacletInfo>(){

                @Override
                public boolean include(TacletInfo itemData) {
                       return !itemData.isNotSupported() && !itemData.isAlreadyInUse();
                }                
        };    


        public LemmaSelectionDialog() {
                this.setTitle("Taclet Selection");
                this.setLayout(new BoxLayout(this.getContentPane(),
                                BoxLayout.X_AXIS));
                this.getContentPane().add(Box.createHorizontalStrut(10));
                this.getContentPane().add(getContentPanel());
                this.getContentPane().add(Box.createHorizontalStrut(10));
                this.setMinimumSize(new Dimension(300, 300));
                this.setLocationByPlatform(true);

                this.pack();

        }

        public ImmutableSet<Taclet> showModal(List<TacletInfo> taclets) {
                this.setModal(true);
                this.getTacletChooser().setItems(taclets, "Taclets");
                this.setVisible(true);
                ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
                for(TacletInfo info : getTacletChooser().getDataOfSelectedItems()){
                        set = set.add(info.getTaclet());
                }
                return set;
        }
        
        private JCheckBox getShowSupported() {
                if(showSupported == null){
                        showSupported = new JCheckBox("Show only supported taclets.");
                        showSupported.setSelected(true);
                        showSupported.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        if(showSupported.isSelected()){
                                                getTacletChooser().addFilter(showOnlySupportedTaclets);
                                                 
                                        }else{
                                                getTacletChooser().removeFilter(showOnlySupportedTaclets);
                                                        
                                        }
                                        
                                }
                        });
                }
                return showSupported;
        }

        private JPanel getButtonPanel() {

                if (buttonPanel == null) {
                        buttonPanel = new JPanel();
                        buttonPanel.setLayout(new BoxLayout(buttonPanel,
                                        BoxLayout.X_AXIS));
                        buttonPanel.add(getShowSupported());
                        buttonPanel.add(Box.createHorizontalGlue());
                        buttonPanel.add(getOkayButton());
                        buttonPanel.add(Box.createHorizontalStrut(8));
                        
                        buttonPanel.add(getCancelButton());
                }
                return buttonPanel;
        }

        private JPanel getContentPanel() {
                if (contentPanel == null) {
                        contentPanel = new JPanel();
                        contentPanel.setLayout(new BoxLayout(contentPanel,
                                        BoxLayout.Y_AXIS));
                        contentPanel.add(Box.createVerticalStrut(10));
                        contentPanel.add(getTacletChooser());
                        contentPanel.add(getButtonPanel());
                        contentPanel.add(Box.createVerticalStrut(10));
                }
                return contentPanel;
        }

        private JButton getOkayButton() {
                if (okayButton == null) {
                        okayButton = new JButton("Okay");
                        okayButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        tacletsSelected();
                                }
                        });
                        okayButton.setPreferredSize(getCancelButton().getPreferredSize());
                }
                return okayButton;
        }
        


        private void tacletsSelected() {

                dispose();
        }

        private void cancel() {
                getTacletChooser().removeSelection();
                getTacletChooser().moveAllToLeft();
                dispose();
        }

        private JButton getCancelButton() {
                if (cancelButton == null) {
                        cancelButton = new JButton("Cancel");
                        cancelButton.addActionListener(new ActionListener() {

                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        cancel();
                                }
                        });
                }
                return cancelButton;
        }

        private ItemChooser<TacletInfo> getTacletChooser() {
                if (tacletChooser == null) {
                        tacletChooser = new ItemChooser<TacletInfo>("Search for taclets with names containing");
                        tacletChooser.addFilterForMovingItems(filterForMovingTaclets);
                        tacletChooser.addFilter(showOnlySupportedTaclets);
                }
                return tacletChooser;
        }

        @Override
        public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {

                return showModal(taclets);
        }

}