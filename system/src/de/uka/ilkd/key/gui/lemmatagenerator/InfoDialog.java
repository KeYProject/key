package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JTextArea;

public class InfoDialog extends JDialog{
        
        private JTextArea infoText;
        private JButton yesButton;
        private JButton noButton;
        private JCheckBox showAgainBox;
        private boolean yesClicked = false;
        
        public InfoDialog(String infoText) {
                this.getContentPane().setLayout(new BoxLayout(this.getContentPane(), BoxLayout.Y_AXIS));
                Box box = Box.createHorizontalBox();
                
                box.add(getShowAgainBox());        
                box.add(Box.createHorizontalGlue());
                getInfoText().setText(infoText);
                this.getContentPane().add(getInfoText());
                this.getContentPane().add(Box.createVerticalStrut(5));
                this.getContentPane().add(box);
                this.getContentPane().add(Box.createVerticalStrut(5));
                box = Box.createHorizontalBox();
                box.add(Box.createHorizontalGlue());
                box.add(getNoButton());                
                box.add(Box.createHorizontalStrut(5));
                box.add(getYesButton());
                this.getContentPane().add(box);
                this.setModal(true);
                this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
                this.pack();
        }
        
        public boolean showDialog(){
                this.setVisible(true);
                return yesClicked;
        }
        
        private JTextArea getInfoText(){
                if(infoText == null){
                        infoText = new JTextArea();
                        infoText.setEditable(false);
                        infoText.setBackground(this.getContentPane().getBackground());
                }
                return infoText;
        }
        
        private JCheckBox getShowAgainBox() {
                if(showAgainBox == null){
                        showAgainBox = new JCheckBox("Don't show this dialog again.");
                        
                }
                return showAgainBox;
        }
        
        private JButton getYesButton(){
                if(yesButton == null){
                        yesButton = new JButton("Proceed");
                        yesButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        yesClicked = true;
                                        InfoDialog.this.dispose();
                                        
                                }
                        });
                }
                return yesButton;
        }
        
        private JButton getNoButton(){
                if(noButton == null){
                        noButton = new JButton("Cancel");
                        noButton.addActionListener(new ActionListener() {
                                
                                @Override
                                public void actionPerformed(ActionEvent e) {
                                        InfoDialog.this.dispose();
                                        
                                }
                        });
                }
                return noButton;
        }
        
        

}
