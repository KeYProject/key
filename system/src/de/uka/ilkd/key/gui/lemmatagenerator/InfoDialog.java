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
