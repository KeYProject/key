package de.uka.ilkd.key.gui;



import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Vector;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.DefaultListModel;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.ListModel;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;


class TacletChooser extends JPanel{
    
    private static final long serialVersionUID = 1L;
    private JList   tacletList;
    private JTextArea detailedInfo;
    private JPanel   contentPanel;
    
    static private final Dimension MAX = new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE);
    
    TacletChooser(){
	this.setMaximumSize(MAX);
	setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
	add(Box.createVerticalStrut(10));
	add(getContentPanel());
	add(Box.createVerticalStrut(10));
	
	
	
    }
    
    private JPanel getContentPanel(){
	if(contentPanel == null){
	    contentPanel = new JPanel();
	    contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.X_AXIS));
	    contentPanel.add(getTacletList());
	    contentPanel.add(Box.createHorizontalStrut(5));
	    contentPanel.add(getDetailedInfo());
	    contentPanel.add(Box.createHorizontalGlue());
	}
	return contentPanel;
    }
    
    private JList getTacletList(){
	if(tacletList == null){
	    tacletList = new JList();
	

	    tacletList.setAlignmentX(LEFT_ALIGNMENT);
	    tacletList.setMaximumSize(MAX);
	    tacletList.setMinimumSize(new Dimension(100,50));
	    tacletList.setBorder(new TitledBorder("Taclets"));
	    tacletList.setCellRenderer(new DefaultListCellRenderer(){
                private static final long serialVersionUID = 1L;
	    public Component getListCellRendererComponent
		    (JList list,
		     Object value,           
		     int index,              
		     boolean isSelected,     
		     boolean cellHasFocus)    
		                             
		{
		    if (value instanceof Taclet) {
			value = ((Taclet)value).name();
		    }
		    return super.getListCellRendererComponent(list, value, 
							      index, 
							      isSelected, 
							      cellHasFocus);
		}
	    });
	}
	return tacletList;
    }
    
    private JTextArea getDetailedInfo(){
	if(detailedInfo == null){
	    detailedInfo = new JTextArea();
	    detailedInfo.setMaximumSize(MAX);
	    detailedInfo.setMinimumSize(new Dimension(100,50));
	    detailedInfo.setBorder(new TitledBorder("Info"));
	}
	return detailedInfo;
    }
    
    public void setTaclets(ImmutableSet<Taclet> taclets){
	Vector<Taclet> vec = new Vector<Taclet>(); 
	for(Taclet taclet : taclets){
	   vec.add(taclet);
	}
	
	getTacletList().setListData(vec);
	
	getTacletList().setSelectionInterval(0, taclets.size()-1);
    }
    
    public ImmutableSet<Taclet> getSelectedTaclets(){
	Object [] selected = getTacletList().getSelectedValues();
	ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
	for(Object obj : selected){
	    set = set.add((Taclet) obj);
	}
	return set;
    }
    
    public void removeSelection(){
	getTacletList().setSelectedIndices(new int[0]);
    }
}


public class LemmaSelectionDialog extends JDialog{
    
    private static final long serialVersionUID = 1L;

    private JButton okayButton;

    private JButton cancelButton;
    private JPanel  buttonPanel;
    private JPanel  contentPanel;
    private TacletChooser  tacletChooser;

    

    LemmaSelectionDialog(){

	this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.X_AXIS));
	this.getContentPane().add(Box.createHorizontalStrut(10));
	this.getContentPane().add(getContentPanel());
	this.getContentPane().add(Box.createHorizontalStrut(10));
	this.setMinimumSize(new Dimension(300,300));

	this.pack();

    }
    
    public ImmutableSet<Taclet> showModal(ImmutableSet<Taclet> taclets){
	this.setModal(true);
	this.getTacletChooser().setTaclets(taclets);
	this.setVisible(true);
	return getTacletChooser().getSelectedTaclets();
    }
    

    
    private JPanel getButtonPanel(){
	
	if(buttonPanel == null){
	    buttonPanel = new JPanel();
	    buttonPanel.setLayout(new BoxLayout(buttonPanel,BoxLayout.X_AXIS));
	    buttonPanel.add(Box.createHorizontalGlue());
	    buttonPanel.add(getOkayButton());
	    buttonPanel.add(Box.createHorizontalStrut(5));
	    buttonPanel.add(getCancelButton());
	}
	return buttonPanel;
    }
    


    
    private JPanel getContentPanel(){
	if(contentPanel == null){
	    contentPanel = new JPanel();
	    contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.Y_AXIS));
	    contentPanel.add(Box.createVerticalStrut(10));
	    contentPanel.add(getTacletChooser());
	    contentPanel.add(getButtonPanel());
	    contentPanel.add(Box.createVerticalStrut(10));
	}
	return contentPanel;
    }
    


    
    private JButton getOkayButton(){
	if(okayButton == null){
	    okayButton = new JButton("select");
	    okayButton.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	        	tacletsSelected();
	        }
	    });
	}
	return okayButton;
    }
    
   
    private void tacletsSelected(){

	dispose();
    }
    
    private void cancel(){
	getTacletChooser().removeSelection();
	dispose();
    }
    
    private JButton getCancelButton(){
	if(cancelButton == null){
	    cancelButton = new JButton("cancel");
	    cancelButton.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	        	cancel();
	        }
	    });
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
