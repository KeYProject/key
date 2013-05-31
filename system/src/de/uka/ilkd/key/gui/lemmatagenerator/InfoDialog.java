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

import java.awt.Component;

import javax.swing.Box;
import javax.swing.JCheckBox;
import javax.swing.JOptionPane;
import javax.swing.JTextPane;

public class InfoDialog {
        private JTextPane infoText;
        private JCheckBox showAgainBox;

        private Box box;
        


        
        public boolean showDialog(String text,Component parent){
                getInfoText().setText(text);
                Object[] options = {"Cancel",
                                    "Continue"};
                int n = JOptionPane.showOptionDialog(parent,
                    getBox(),
                    "Warning",
                    JOptionPane.YES_NO_CANCEL_OPTION,
                    JOptionPane.WARNING_MESSAGE,
                    null,
                    options,
                    options[0]);
                return n == 1;
        }
        
        
        public boolean showThisDialogNextTime(){
                return !showAgainBox.isSelected();
        }
        
        private Box getBox(){
                if(box == null){
                        box = Box.createVerticalBox();
                        box.add(getInfoText());
                        box.add(getShowAgainBox());
                        getInfoText().setBackground(box.getBackground());
                }
                return box;
        }
                
        private JTextPane getInfoText(){
                if(infoText == null){
                        infoText = new JTextPane();
                        infoText.setEditable(false);
                             }
                return infoText;
        }
        
        private JCheckBox getShowAgainBox() {
                if(showAgainBox == null){
                        showAgainBox = new JCheckBox("Don't show this dialog again.");
                        
                }
                return showAgainBox;
        }
        
     
        
        

}