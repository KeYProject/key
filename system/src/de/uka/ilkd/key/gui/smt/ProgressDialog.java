// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.ScrollPane;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;


import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;

import javax.swing.AbstractAction;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.SwingUtilities;

public class ProgressDialog extends JDialog {

    private static final long serialVersionUID = 1L;
    private ScrollPane scrollPane;
    private JPanel     panelContainer;
    private JPanel     buttonContainer;
    private JPanel     infoPanel;
    private JButton    discardButton;
    private JButton    applyButton;
    private JButton    stopButton;
    private JLabel     infoLabel;
    private JButton    exceptionButton;
    private JPopupMenu      exceptionMenu;
    private final ProgressPanel [] panels ;

    
    
    
    
    public ProgressDialog(ProgressPanel [] panels, ActionListener alDiscardButton,
	                                              ActionListener alApplyButton,
	                                              ActionListener alStopButton){

	this.panels = panels;
	for(ProgressPanel panel : panels){
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
	setDefaultCloseOperation(DISPOSE_ON_CLOSE);
	setModal(true);

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
    
    private JPanel getInfoPanel(){
	if(infoPanel == null){
	    infoPanel = new JPanel();
	    infoPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
	    
	    infoPanel.add(getExceptionButton());
	    //infoPanel.add(getInfoLabel());
	}
	return infoPanel;
    }
    
    private JButton getExceptionButton(){
	if(exceptionButton == null){
	    exceptionButton = new JButton();
	    exceptionButton.addActionListener(new ExceptionButtonListener());
	    exceptionButton.setText("Exception!");
	    exceptionButton.setVisible(false);
	   
	}
	return exceptionButton;
    }
    
    private JLabel getInfoLabel(){
	if(infoLabel == null){
	    infoLabel = new JLabel();
	    infoLabel.setAlignmentX(CENTER_ALIGNMENT);
	    infoLabel.setAlignmentY(CENTER_ALIGNMENT);
	}
	return infoLabel;
    }
    
    private JPanel getButtonContainer(){
	if(buttonContainer == null){
	    buttonContainer = new JPanel();
	    buttonContainer.setLayout(new BoxLayout(buttonContainer, BoxLayout.X_AXIS));
	    
	   // buttonContainer.add(Box.createHorizontalGlue());
	    buttonContainer.add(getInfoPanel());
	    buttonContainer.add(Box.createHorizontalStrut(10));
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
    
    private JPopupMenu getExceptionMenu(){
	if(exceptionMenu == null){
	    exceptionMenu = new JPopupMenu();
	}
	return exceptionMenu;
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
    
    public void setInfo(String text){
	getInfoLabel().setText(text);
    }
    
    public void setInfo(String text, Collection<Point> singlePanels){
	getExceptionButton().setText(text);
	
	exceptionMenu = new JPopupMenu();
	for(final Point singlePanel : singlePanels){
	    if(singlePanel.x>=0 && singlePanel.x < panels.length){
	    JMenuItem item = new JMenuItem(new AbstractAction(
		    panels[singlePanel.x].getTitle(singlePanel.y)) {
	        private static final long serialVersionUID = 1L;

		@Override
	        public void actionPerformed(ActionEvent e) {
		    panels[singlePanel.x].showInfo(singlePanel.y);
	        }
	    });
	 
	    exceptionMenu.add(item);
	  }
	}
	getExceptionButton().setVisible(true);
	
    }
    
    public void setInfoColor(Color color){
	getExceptionButton().setForeground(color);
	getInfoLabel().setForeground(color);
    }
    
    private class ExceptionButtonListener implements ActionListener{
	@Override
	public void actionPerformed(ActionEvent e) {
	    JPopupMenu menu = getExceptionMenu();
            int width = Math.max(menu.getPreferredSize().width,getExceptionButton().getWidth());
                menu.setPopupSize(width, menu.getPreferredSize().height);
                menu.show(getExceptionButton(),0 ,getExceptionButton().getHeight());
	}
    }
    
    
    
    

}
