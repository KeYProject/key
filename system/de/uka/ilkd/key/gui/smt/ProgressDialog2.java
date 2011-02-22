package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.ScrollPane;
import java.awt.event.ActionListener;
import java.util.Collection;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;

public class ProgressDialog2 extends JDialog {
    
    private ScrollPane scrollPane;
    private JPanel     panelContainer;
    private JPanel     buttonContainer;
    private JButton    discardButton;
    private JButton    applyButton;
    private JButton    stopButton;
    private ProgressPanel2 []panels;
    
    
    
    
    public ProgressDialog2(ProgressPanel2 [] panels, ActionListener alDiscardButton,
	                                              ActionListener alApplyButton,
	                                              ActionListener alStopButton){
	this.panels = panels;
	for(ProgressPanel2 panel : panels){
	    panel.setAlignmentX(LEFT_ALIGNMENT);
	    
	    panel.setMaximumSize(new Dimension(Integer.MAX_VALUE,50));
	    getPanelContainer().add(panel);
	}
	this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.PAGE_AXIS));
	
	this.getContentPane().add(getScrollPane());
	this.getContentPane().add(Box.createVerticalStrut(5));
	this.getContentPane().add(getButtonContainer());
	this.getContentPane().add(Box.createVerticalStrut(5));
	this.setSize(500, 250);
	this.setResizable(false);
	this.setTitle("Progress Dialog");
	getDiscardButton().addActionListener(alDiscardButton);
	getApplyButton().addActionListener(alApplyButton);
	getStopButton().addActionListener(alStopButton);

    }
    
    private JPanel getPanelContainer(){
	if(panelContainer == null){
	   panelContainer = new JPanel();
	   panelContainer.setLayout(new BoxLayout(panelContainer, BoxLayout.PAGE_AXIS));
	   panelContainer.setBackground(Color.WHITE);
	   panelContainer.setMaximumSize(new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE));
	}
	return panelContainer;
    }
    
    private JPanel getButtonContainer(){
	if(buttonContainer == null){
	    buttonContainer = new JPanel();
	    buttonContainer.setLayout(new BoxLayout(buttonContainer, BoxLayout.X_AXIS));
	    buttonContainer.add(Box.createHorizontalGlue());
	    buttonContainer.add(getDiscardButton());
	    buttonContainer.add(Box.createHorizontalStrut(10));
	    buttonContainer.add(getApplyButton());
	    buttonContainer.add(Box.createHorizontalStrut(10));
	    buttonContainer.add(getStopButton());
	    buttonContainer.add(Box.createHorizontalStrut(10));
	    buttonContainer.setMaximumSize(new Dimension(Integer.MAX_VALUE,getDiscardButton().getPreferredSize().height+10));
	}
	return buttonContainer;
    }
    
    private JButton getDiscardButton(){
	if(discardButton == null){
	    discardButton = new JButton();
	    discardButton.setText("Discard");
	    discardButton.setAlignmentX(LEFT_ALIGNMENT);
	}
	return discardButton;
    }
    
    private JButton getApplyButton(){
	if(applyButton == null){
	    applyButton = new JButton();
	    applyButton.setText("Apply");
	    applyButton.setAlignmentX(LEFT_ALIGNMENT);
	}
	return applyButton;
    }
    
    private JButton getStopButton(){
	if(stopButton == null){
	    stopButton = new JButton();
	    stopButton.setText("Stop");
	    stopButton.setAlignmentX(LEFT_ALIGNMENT);
	}
	return stopButton;
    }
    
    private ScrollPane getScrollPane(){
	if(scrollPane == null){
	    scrollPane = new ScrollPane();
	    scrollPane.add(getPanelContainer());
	}
	return scrollPane;
    }
    
    public void setApplyButtonEnabled(final boolean b){
	SwingUtilities.invokeLater(new Runnable() {
	    @Override
	    public void run() {
		getApplyButton().setEnabled(b);		
	    }
	});
    }
    
    public void setDiscardButtonEnabled(final boolean b){
	SwingUtilities.invokeLater(new Runnable() {
	    @Override
	    public void run() {
		getDiscardButton().setEnabled(b);		
	    }
	});
    }
    
    
    public void setStopButtonEnabled(final boolean b){
	SwingUtilities.invokeLater(new Runnable() {
	    @Override
	    public void run() {
		getStopButton().setEnabled(b);		
	    }
	});
    }
    
    
    
    
    
    
    

}
