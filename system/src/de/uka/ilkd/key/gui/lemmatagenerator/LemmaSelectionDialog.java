package de.uka.ilkd.key.gui.lemmatagenerator;



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
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.TacletSoundnessPOLoader.TacletInfo;


class TacletChooser extends JPanel{
    
    private static final long serialVersionUID = 1L;
    private JList   tacletList;
    private JList    selectedList;
    private JPanel  middlePanel;
    private JPanel   contentPanel;
    private JButton  leftButton;
    private JButton  rightButton;
    private JScrollPane leftPane;
    private JScrollPane rightPane;
    
    private final DefaultListCellRenderer cellRenderer = new DefaultListCellRenderer(){
	
	private  String createAdditonalInfo(TacletInfo info){
	    String s = "";
	    if(info.isNotSupported()){
		return " (is not supported)";
	    }
	    if(info.isAlreadyInUse()){
		return " (is already in use)";
	    }
	    return s;
	}
	
        private static final long serialVersionUID = 1L;
	    public Component getListCellRendererComponent
		    (JList list,
		     Object value,           
		     int index,              
		     boolean isSelected,     
		     boolean cellHasFocus)    
		                             
		{
		    if (value instanceof TacletInfo) {
			TacletInfo info = ((TacletInfo)value);
			value = info.getTaclet().name().toString() + 
			createAdditonalInfo(info);
		    }
		    return super.getListCellRendererComponent(list, value, 
							      index, 
							      isSelected, 
							      cellHasFocus);
		}
	    };
    
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
	    contentPanel.add(getLeftPane());
	    contentPanel.add(Box.createHorizontalStrut(5));
	    contentPanel.add(getMiddlePanel());
	    contentPanel.add(Box.createHorizontalStrut(5));
	    contentPanel.add(getRightPane());
	    contentPanel.add(Box.createHorizontalGlue());
	}
	return contentPanel;
    }
    
    private JScrollPane getLeftPane(){
	if(leftPane == null){
	  
	    leftPane = new JScrollPane(getTacletList(),ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
		    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED
		    );
	    leftPane.setMaximumSize(MAX);
	    leftPane.setBorder(new TitledBorder("Choice"));
	}
	return leftPane;
    }
    
    private JScrollPane getRightPane(){
	if(rightPane == null){
	    rightPane = new JScrollPane(getSelectedList(),ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
		    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED
		    );
	    rightPane.setMaximumSize(MAX);
	    rightPane.setBorder(new TitledBorder("Selected"));
	}
	return rightPane;
    }
    
    private JPanel getMiddlePanel(){
	if(middlePanel == null){
	    middlePanel = new JPanel();
	    middlePanel.setLayout(new BoxLayout(middlePanel, BoxLayout.Y_AXIS));
	    middlePanel.add(getLeftButton());
	    middlePanel.add(Box.createVerticalStrut(10));
	    middlePanel.add(getRightButton());
	    Dimension dim = getLeftButton().getPreferredSize();
	    dim.height = dim.height+10 + getRightButton().getPreferredSize().height;
	    middlePanel.setMaximumSize(dim);
	    
	}
	return middlePanel;
    }
    
    private JButton getLeftButton(){
	if(leftButton == null){
	    leftButton = new JButton("<");
	    leftButton.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	            cut(getSelectedList().getSelectedValues(),getSelectionModel(),getTacletModel(),
	        	    getTacletList());
	        }
	    });
	}
	return leftButton;
	    
    }
    
    private JButton getRightButton(){
	if(rightButton == null){
	    rightButton = new JButton(">");
	    rightButton.addActionListener(new ActionListener() {
	        
	        @Override
	        public void actionPerformed(ActionEvent e) {
	            
	            cut(getTacletList().getSelectedValues(),getTacletModel(),getSelectionModel(),
	        	    getSelectedList());
	        }
	    });
	}
	return rightButton;
	    
    }

    private void cut(Object [] values, DefaultListModel src, DefaultListModel dest, JList destList){
	if(values.length == 0){
	    return;
	}
	int added =0;
	for(Object value : values){
	    TacletInfo info = (TacletInfo) value;
	    if(!info.isAlreadyInUse() && !info.isNotSupported()){
		src.removeElement(value);
		dest.addElement(value);
		added++;
	    }
	    
	}
	if(added>0){
	destList.setSelectionInterval(dest.size()-added, dest.size()-1);
	}
    }
    
    
    private JList getTacletList(){
	if(tacletList == null){
	    tacletList = new JList();
	
	    tacletList.setModel(new DefaultListModel());
	    tacletList.setCellRenderer(cellRenderer);
	}
	return tacletList;
    }
    
    private JList getSelectedList(){
	if(selectedList == null){
	    selectedList = new JList();
	
	    selectedList.setModel(new DefaultListModel());
	    selectedList.setCellRenderer(cellRenderer);
	}
	return selectedList;
    }
    
    private DefaultListModel getSelectionModel(){
	return (DefaultListModel)(getSelectedList().getModel());
    }
    
    private DefaultListModel getTacletModel(){
	return (DefaultListModel)(getTacletList().getModel());
    }
    
    public void setTaclets(Vector<TacletInfo> taclets){
	
	DefaultListModel model = getTacletModel();
	for(TacletInfo info : taclets){
	    model.addElement(info);
	}
	getTacletList().setModel(model);
	
	getTacletList().setSelectionInterval(0, taclets.size()-1);
    }
    
    public ImmutableSet<Taclet> getSelectedTaclets(){
	
	Object [] selected = getSelectionModel().toArray();
	ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
	for(Object obj : selected){
	    set = set.add(((TacletInfo) obj).getTaclet());
	}
	return set;
    }
    
    public void removeSelection(){
	getSelectedList().setSelectedIndices(new int[0]);
	getTacletList().setSelectedIndices(new int[0]);
    }
}

public class LemmaSelectionDialog extends JDialog implements TacletFilter{
    
    private static final long serialVersionUID = 1L;

    private JButton okayButton;

    private JButton cancelButton;
    private JPanel  buttonPanel;
    private JPanel  contentPanel;
    private TacletChooser  tacletChooser;

    

    public LemmaSelectionDialog(){
	this.setTitle("Taclet Selection");
	this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.X_AXIS));
	this.getContentPane().add(Box.createHorizontalStrut(10));
	this.getContentPane().add(getContentPanel());
	this.getContentPane().add(Box.createHorizontalStrut(10));
	this.setMinimumSize(new Dimension(300,300));
	this.setLocationByPlatform(true);

	this.pack();

    }
    
    public ImmutableSet<Taclet> showModal(Vector<TacletInfo> taclets){
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
	    okayButton = new JButton("ok");
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

    @Override
    public ImmutableSet<Taclet> filter(Vector<TacletInfo> taclets) {
	return showModal(taclets);
    }
    
    
}
