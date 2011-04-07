package de.uka.ilkd.key.gui;



import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JTextArea;


class TacletChooser extends JPanel{
    private static final long serialVersionUID = 1L;
    private JList   tacletList;
    private JTextArea detailedInfo;
    static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE);
    
    TacletChooser(){
	this.setMaximumSize(MAX);
	setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
	this.setBackground(Color.RED);
	this.setAlignmentX(LEFT_ALIGNMENT);
	add(getTacletList());
	add(Box.createHorizontalStrut(5));
	add(getDetailedInfo());
	add(Box.createHorizontalGlue());
	
    }
    
    private JList getTacletList(){
	if(tacletList == null){
	    tacletList = new JList();
	    DefaultListModel model = new DefaultListModel();
	    model.addElement("Hallo");
	    tacletList.setAlignmentX(LEFT_ALIGNMENT);
	    tacletList.setModel(model);
	    tacletList.setMaximumSize(MAX);
	}
	return tacletList;
    }
    
    private JTextArea getDetailedInfo(){
	if(detailedInfo == null){
	    detailedInfo = new JTextArea();
	    detailedInfo.setMaximumSize(MAX);
	    detailedInfo.setText("adads");
	}
	return detailedInfo;
    }
}


public class LemmaSelectionDialog extends JDialog{
    enum State  {FileSelection,TacletSelection};
    
    private static final long serialVersionUID = 1L;

    private JButton okayButton;
    private JButton backButton;
    private JButton cancelButton;
    private JPanel  buttonPanel;
    private JLabel  infoLabel;
    private JPanel  infoPanel;
    private JPanel  contentPanel;
    private JFileChooser fileChooser;
    private TacletChooser  tacletChooser;
    private State    state = State.FileSelection;
    

    LemmaSelectionDialog(){

	this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.Y_AXIS));
	this.getContentPane().add(Box.createVerticalStrut(10));
	this.getContentPane().add(getInfoPanel());
	this.getContentPane().add(getContentPanel());
	this.getContentPane().add(getButtonPanel());
	this.getContentPane().add(Box.createVerticalStrut(5));
	this.pack();
	this.setVisible(true);
    }
    

    
    private JFileChooser getFileChooser(){
	if(fileChooser == null){
	    fileChooser = new JFileChooser();
	    fileChooser.setControlButtonsAreShown(false);
	}
	return fileChooser;
    }
    
    private JPanel getButtonPanel(){
	
	if(buttonPanel == null){
	    buttonPanel = new JPanel();
	    buttonPanel.setLayout(new BoxLayout(buttonPanel,BoxLayout.X_AXIS));
	    buttonPanel.add(Box.createHorizontalGlue());
	    buttonPanel.add(getOkayButton());
	    buttonPanel.add(Box.createHorizontalStrut(5));
	    buttonPanel.add(getCancelButton());
	    buttonPanel.add(Box.createHorizontalStrut(getFileChooser().getInsets().right));
	    
	}
	return buttonPanel;
    }
    
    private JPanel getInfoPanel(){
	if(infoPanel == null){
	    infoPanel = new JPanel();
	    infoPanel.setLayout(new BoxLayout(infoPanel, BoxLayout.X_AXIS));
	    infoPanel.add(Box.createHorizontalStrut(getFileChooser().getInsets().left));
	    infoPanel.add(getInfoLabel());
	    infoPanel.add(Box.createHorizontalGlue());
	}
	return infoPanel;
    }
    
    private JLabel getInfoLabel(){
	if(infoLabel == null){
	    infoLabel = new JLabel("Please choose the file that contains the taclets:");
	}
	return infoLabel;
    }
    
    private JPanel getContentPanel(){
	if(contentPanel == null){
	    
	    contentPanel = new JPanel();
	    contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.X_AXIS));
	    contentPanel.add(getFileChooser());
	}
	return contentPanel;
    }
    

    
    private JButton getBackButton(){
	if(backButton == null){
	    backButton = new JButton("back");
	}
	return backButton;
    }
    
    private JButton getOkayButton(){
	if(okayButton == null){
	    okayButton = new JButton("select");
	    okayButton.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	            if(state == State.FileSelection){
	        	fileSelected();
	        	state = State.TacletSelection;
	            }else
	            if(state == State.TacletSelection){
	        	tacletsSelected();
	            }
	        }
	    });
	}
	return okayButton;
    }
    
    private void fileSelected(){
        getContentPanel().removeAll();
        getContentPanel().add(Box.createHorizontalStrut(getFileChooser().getInsets().left));
        getContentPanel().add(getTacletChooser());
        //Dimension dim = new Dimension(Math.max(getInfoPanel().getWidth(),getTacletChooser().getPreferredSize().width),
        //	                      getTacletChooser().getPreferredSize().height);
       // getTacletChooser().setPreferredSize(dim);
        pack();
    }
    
    private void tacletsSelected(){
	this.dispose();
    }
    
    private JButton getCancelButton(){
	if(cancelButton == null){
	    cancelButton = new JButton("cancel");
	}
	return cancelButton;
    }
    
    private TacletChooser getTacletChooser(){
	if(tacletChooser == null){
	    tacletChooser = new TacletChooser();
	}
	return tacletChooser;
    }
    
    
}
