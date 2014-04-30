// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.smt;


import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;
import java.util.LinkedList;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JPopupMenu;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import de.uka.ilkd.key.gui.IconFactory;

public class ComplexButton {
    
    
    
    private JButton selectionComponent;
    private JButton actionComponent;
    private Action [] items;
    private EmptyAction  emptyItem = new EmptyAction();
    private Action  selectedItem = emptyItem;
    private String prefix = "";
    private int iconSize;
    private Collection<ChangeListener> listeners = new LinkedList<ChangeListener>();
    // Is the menu showing?
    private boolean showing;

    private int oldWidth;

    
    
    private JPopupMenu menu ;
    
    
    public JComponent getSelectionComponent(){
	return getSelectionButton();
	
    }
    
    public ComplexButton(int iconSize){
	this.iconSize = iconSize;
	
    }
    
    
    public void setEnabled(boolean b){
	if(items.length == 0){
	    b = false;
	}
	getActionButton().setEnabled(b);
	//getAction().setEnabled(b);
	
    }
    
    public void addListener(ChangeListener listener){
	listeners.add(listener);
    }
    
    public void removeListener(ChangeListener listener){
	listeners.remove(listener);
    }
    
      
    public JComponent getActionComponent(){
	return getActionButton();
    }
    
    public void setAction(Action action){
	getActionButton().setAction(action);
    }
    
    public Action getAction(){
	return getActionButton().getAction();
    }
    
    public Object getSelectedItem(){
	return selectedItem;
    }
    
    public Object getEmptyItem(){
	return emptyItem;
    }
    
    public void setEmptyItem(String text, String toolTip){
	boolean update = isEmptyItem();
	emptyItem.setText(text);
	emptyItem.setToolTip(toolTip);
	if(update){
	    selectedItem = emptyItem;
	    
	    update();
	}
	
    }
    
    public void setPrefix(String s){
	prefix = s;
    }
    
    public boolean isEmptyItem(){
	return selectedItem == emptyItem;
    }
    
    void update(){
	setAction(selectedItem);
	if(getAction() != null){
	    
	    getAction().putValue(Action.NAME,isEmptyItem() ? selectedItem.toString(): prefix + selectedItem.toString());  
	    if(isEmptyItem()){
		getAction().putValue(Action.SHORT_DESCRIPTION,emptyItem.getToolTip());
	    }
	}

    }
    
    public boolean contains(Action item){
	for(Object it : items){
	    if(it.equals(item)){
		return true;
	    }
	}
	return false;
    }

    
    public void setSelectedItem(Action item){
	if(item == null || (!contains(item)&& item != emptyItem)){
	    return;
	}

	
	selectedItem = item;
	for(ChangeListener l : listeners){
	    l.stateChanged(new ChangeEvent(this));
	}
	update();
    }
    
    
    
    JButton getSelectionButton(){
	if(selectionComponent == null){
	    selectionComponent = new JButton();
	    selectionComponent.setFocusable(false);
	    selectionComponent.addActionListener(new ActionListener() {
	        public void actionPerformed(ActionEvent e) {
	            if(items.length == 0){
	        	return;
	            }
	            

                    if (showing) {
                        showing = false;
                        // the menu is already cleared by
                        // clicking the button
                    } else {
	                int width = Math.max(oldWidth,
                            getSelectionComponent().getWidth()+getActionButton().getWidth());
	                menu.setPopupSize(width, menu.getPreferredSize().height);
                        showing = true;
	                menu.show(getActionButton(),0 ,getActionButton().getHeight());
                    }
	        }
	    });
	 
	   
	    selectionComponent.setIcon(IconFactory.selectDecProcArrow(iconSize));
	}
	return selectionComponent;
    }
    
    JButton getActionButton(){
	if(actionComponent == null){
	    actionComponent = new JButton();
	    actionComponent.addChangeListener(new ChangeListener() {
	        
	        public void stateChanged(ChangeEvent arg0) {
	    		getSelectionButton().setEnabled(actionComponent.isEnabled());
	        }
	    });
	}
	return actionComponent;
    }
    
    JPopupMenu getMenu(){
	if(menu == null){
	    menu = createMenu();    
	}	
	return menu;
    }
    
    JPopupMenu createMenu(){
	menu = new JPopupMenu();


	return menu;
    }
    
    public void setItems(Action[]  it){

	items = it;
	createMenu();
	if(it == null){
	  items = new Action[0];   
	}
	
	for(Action content : items){	    
	    getMenu().add(new ItemAction(content));   
	}
	oldWidth = menu.getPreferredSize().width;
  
        if(items.length == 0){
            setSelectedItem(emptyItem);
            setEnabled(false);
        }
        
    }
    
    public  Object getTopItem(){
	if(items.length > 0){
	    return items[0];
	}
	return emptyItem;
    }
    
  
    
    public class EmptyAction extends AbstractAction{


        private static final long serialVersionUID = 1L;
	String text;
	String toolTip;
	
	public EmptyAction() {
	   setText("empty");
        } 
	
	public void setText(String t){
	    text = t;
	    putValue(Action.NAME, text);
	    putValue(Action.SHORT_DESCRIPTION,toolTip);
	}
	
	public void setToolTip(String t){
	    toolTip = t;
	}
	
	public String getToolTip(){
	    return toolTip;
	}
	
	public String toString(){
	    return text;
	}

	@Override
	public boolean isEnabled() {
	    return false;
	}
		
        public void actionPerformed(ActionEvent arg0) {
	    showing = false;
        }
    }
    
    

    
    class ItemAction extends AbstractAction{
	private static final long serialVersionUID = 1L;
	private Action content;

	ItemAction(Action content){
	    this.content = content;
	    putValue(Action.NAME, content.toString());
	}

	public void actionPerformed(ActionEvent e) {
	    showing = false;
	    setSelectedItem(content);
	}
	


	
	public String toString(){
	    return content.toString();
	}
    }
    
}