package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Image;
import java.awt.Insets;
import java.awt.Polygon;
import java.awt.RenderingHints;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTextPane;
import javax.swing.text.StyledEditorKit;
import javax.swing.text.View;

import de.uka.ilkd.key.gui.IconFactory;

public class InfoDialog extends JDialog{
        private static final long serialVersionUID = 1L;
        private JTextPane infoText;
        private JButton yesButton;
        private JButton noButton;
        private JCheckBox showAgainBox;
        private boolean yesClicked = false;
        
        private static class Warning extends JPanel{
                Dimension dim = new Dimension(60,60);
                Image img = IconFactory.keyWarning(dim.width,dim.height).getImage();
                public Warning() {
                        
                                Dimension size = new Dimension(dim.width+40,dim.height+40);
                                setPreferredSize(size);
                                setMinimumSize(size);
                                setMaximumSize(size);
                                setSize(size);
                                setLayout(null);
                }
        

                    public void paintComponent(Graphics g) {
                        ((Graphics2D)g).setRenderingHint(RenderingHints.KEY_ANTIALIASING,RenderingHints.VALUE_ANTIALIAS_ON);
                        g.drawImage(img,20,20,null);
                    }
                
               
        }
        
        public InfoDialog(String infoText) {
                this.getContentPane().setLayout(new BoxLayout(this.getContentPane(), BoxLayout.Y_AXIS));
                Box box = Box.createHorizontalBox();
                getInfoText().setText(infoText);
                box.add(new Warning());
                box.add(getInfoText());
                this.getContentPane().add(box);
                
                box = Box.createHorizontalBox();
                box.add(getShowAgainBox());        
                box.add(Box.createHorizontalGlue());
           
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
                this.setLocationByPlatform(true);
                //System.out.println(getInfoTextHeight());
               // this.getInfoText().setPreferredSize(new Dimension(400, getInfoTextHeight()));
                this.setMaximumSize(new Dimension(500,Integer.MAX_VALUE));
                this.setPreferredSize(new Dimension(500,400));
                this.getInfoText().setMaximumSize(new Dimension(400,Integer.MAX_VALUE));
                this.getInfoText().setPreferredSize(new Dimension(400, getInfoTextHeight()));
                this.pack();
             
        }
        
        public int getInfoTextHeight() {
                int height = getInfoText().getFontMetrics(getInfoText().getFont()).getHeight();
                Insets sets = getInfoText().getBorder().getBorderInsets(getInfoText());
                height += sets.bottom +sets.top;
                return (int)getInfoText().getUI().getRootView(getInfoText()).getPreferredSpan(View.Y_AXIS);
        }
        
        public boolean showDialog(){
                this.setVisible(true);
                return yesClicked;
        }
        
        public boolean showThisDialogNextTime(){
                return !showAgainBox.isSelected();
        }
        
        private JTextPane getInfoText(){
                if(infoText == null){
                        infoText = new JTextPane();
                        infoText.setEditable(false);
                        infoText.setBackground(this.getContentPane().getBackground());
                        //infoText.setLineWrap(true);
                        //infoText.setWrapStyleWord(true);
                        infoText.setFont(infoText.getFont()
                                        .deriveFont(infoText.getFont().getSize()*1.5f));
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
        
        public static void main(String [] args){
                System.out.println("Start");
                InfoDialog dialog =    new InfoDialog("adadjhafb jshbgfd jbsjfdbs jfdbsjdfbsjhfbjsfbjs asdasda asd asdasd ads adadjhafb jshbgfd jbsjfdbs jfdbsjdfbsjhfbjsfbjs asdasda asd asdasd ads adadjhafb jshbgfd jbsjfdbs jfdbsjdfbsjhfbjsfbjs asdasda asd asdasd ads adadjhafb jshbgfd jbsjfdbs jfdbsjdfbsjhfbjsfbjs asdasda asd asdasd ads adadjhafb jshbgfd jbsjfdbs jfdbsjdfbsjhfbjsfbjs asdasda asd asdasd ads");
                
                dialog.showDialog();
         
        }
        
        

}
