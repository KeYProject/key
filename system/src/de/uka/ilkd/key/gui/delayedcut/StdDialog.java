package de.uka.ilkd.key.gui.delayedcut;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;

import javax.swing.Box;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;


public class StdDialog extends JDialog{

    private static final long serialVersionUID = 1L;
    private JButton helpButton;
    private JButton okayButton;
    private JButton cancelButton;
    private boolean okayButtonHasBeenPressed = false;
    private boolean cancelButtonHasBeenPressed = false;
    
    public StdDialog(String title, JComponent content, int strut, boolean helpButton) {
        this.setLocationByPlatform(true);       
        this.setTitle(title);
        this.setModal(true);
        Dimension dim = content.getMaximumSize();
        dim.width = Integer.MAX_VALUE;
        content.setMaximumSize(dim);
        Box vertBox = Box.createVerticalBox();
        Box horzBox = Box.createHorizontalBox();
        
        vertBox.add(Box.createVerticalStrut(strut));
        
        horzBox.add(Box.createHorizontalStrut(strut));
        horzBox.add(content);
        horzBox.add(Box.createHorizontalGlue());
        horzBox.add(Box.createHorizontalStrut(strut));
        vertBox.add(horzBox);
        vertBox.add(Box.createVerticalStrut(strut));
        horzBox = Box.createHorizontalBox();
        horzBox.add(Box.createHorizontalStrut(strut));
        if(helpButton) {
            horzBox.add(getHelpButton());
            horzBox.add(Box.createHorizontalStrut(strut));
        }
        horzBox.add(Box.createHorizontalGlue());
        horzBox.add(getOkayButton());
        horzBox.add(Box.createHorizontalStrut(strut));
        horzBox.add(getCancelButton());
        vertBox.add(horzBox);
        vertBox.add(Box.createVerticalStrut(strut));        
        this.getContentPane().add(vertBox);
        this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        this.addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosing(WindowEvent e) {
                getCancelButton().doClick();                
            }
        });
        this.pack();
    }
    
    public boolean okayButtonHasBeenPressed() {
        return okayButtonHasBeenPressed;
    }
    
    public boolean cancelButtonHasBeenPressed() {
        return cancelButtonHasBeenPressed;
    }
    
    public JButton getHelpButton() {
        if(helpButton == null){
            helpButton = new JButton("Help");
        }
        return helpButton;
    }
    
    public JButton getOkayButton() {
        if(okayButton == null){
            okayButton = new JButton("Okay");
            okayButton.addActionListener(new ActionListener() {
                
                @Override
                public void actionPerformed(ActionEvent e) {
                    okayButtonHasBeenPressed = true;
                    StdDialog.this.dispose();
                    
                }
            });
        }
        return okayButton;
    }
    
    public JButton getCancelButton() {
        if(cancelButton == null){
            cancelButton = new JButton("Cancel");
            cancelButton.addActionListener(new ActionListener() {
                
                @Override
                public void actionPerformed(ActionEvent e) {
                    cancelButtonHasBeenPressed = true;
                    StdDialog.this.dispose();
                }
            });
        }
        return cancelButton;
    }
    
    public static void main(String [] args) {
        StdDialog dialog = new StdDialog("Test",new JButton("Test"), 5,true);
        dialog.setModal(true);
        dialog.setVisible(true);
    }
}
