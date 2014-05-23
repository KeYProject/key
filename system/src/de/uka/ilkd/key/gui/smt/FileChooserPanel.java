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

package de.uka.ilkd.key.gui.smt;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.LinkedList;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

public class FileChooserPanel extends JPanel{
        private static final long serialVersionUID = 1L;
        private JCheckBox saveToFileBox = null;
        private JTextField folderField = null;
        private JButton chooseButton = null;
        private JTextArea saveToFileExplanation = null;
        private LinkedList<ActionListener> listeners = new LinkedList<ActionListener>();
        
        public String getPath(){
                return getFolderField().getText();
        }
        
        public boolean isSelected(){
                return getSaveToFileBox().isSelected();
        }
        
        
        public FileChooserPanel(boolean withSelection,boolean enabled, String title) {

     

            setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
            setBorder(BorderFactory.createTitledBorder(null, title,
                TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, null));
            
            Box box = Box.createHorizontalBox();
            box.add(getFolderField());
            box.add(Box.createHorizontalStrut(5));
            box.add(getChooseButton());
            add(box);
            if(withSelection){
                    box = Box.createHorizontalBox();
                    box.add(getSaveToFileBox());
                    box.add(Box.createHorizontalGlue());
                    add(box);
                    setActivationMode(enabled);
            }
        }
        
        public FileChooserPanel(boolean withSelection,boolean enabled, String title,String defaultValue) {
            this(withSelection,enabled,title);
            this.getFolderField().setText(defaultValue);
        }
        

        /**
         * This method initializes saveToFileBox    
         *  
         * @return javax.swing.JCheckBox    
         */
        public JCheckBox getSaveToFileBox() {
            if (saveToFileBox == null) {
             
                saveToFileBox = new JCheckBox();
                saveToFileBox.setAlignmentX(LEFT_ALIGNMENT);
                saveToFileBox.addActionListener(new ActionListener() {
                        
                        @Override
                        public void actionPerformed(ActionEvent e) {
                                setActivationMode(saveToFileBox.isSelected());
                                changed();
                        }

                
                });
                saveToFileBox.setText("activated");
            }
            return saveToFileBox;
        }

        private void setActivationMode(boolean selected) {
              getFolderField().setEnabled(selected);
              getChooseButton().setEnabled(selected);
        }
        
        public void addActionListener(ActionListener listener){
                listeners.add(listener);
        }
        
        private void changed(){
                for(ActionListener listener : listeners){
                        listener.actionPerformed(null);
                }
        }
        
        /**
         * This method initializes folderField  
         *  
         * @return javax.swing.JTextField   
         */
        public JTextField getFolderField() {
            if (folderField == null) {
                folderField = new JTextField();
                folderField.getDocument().addDocumentListener(new DocumentListener() {
                        
                        @Override
                        public void removeUpdate(DocumentEvent e) {changed();}
                        
                        @Override
                        public void insertUpdate(DocumentEvent e) {changed();}
                        
                        @Override
                        public void changedUpdate(DocumentEvent e) {changed();}
                });
            }
            return folderField;
        }

        /**
         * This method initializes chooseButton 
         *  
         * @return javax.swing.JButton  
         */
        public JButton getChooseButton() {
            if (chooseButton == null) {
                chooseButton = new JButton();
                chooseButton.setText("choose folder");
                chooseButton.addActionListener(new ActionListener() {
                    
                    public void actionPerformed(ActionEvent e) {
                    JFileChooser chooser = new JFileChooser();
                    chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
                    if(chooser.showDialog(FileChooserPanel.this, "Choose folder") 
                        == JFileChooser.APPROVE_OPTION){
                        getFolderField().setText(chooser.getSelectedFile().getAbsolutePath()); // was: "/%d_%t_%i_%s"
                    }
                    }
                });
            }
            return chooseButton;
        }

        /**
         * This method initializes saveToFileExplanation    
         *  
         * @return javax.swing.JTextArea    
         */
        public JTextArea getSaveToFileExplanation() {
            if (saveToFileExplanation == null) {
                saveToFileExplanation = new JTextArea();
                saveToFileExplanation.setLineWrap(true);
                saveToFileExplanation.setText("Explanation of this field....");
            }
            return saveToFileExplanation;
        }
    }