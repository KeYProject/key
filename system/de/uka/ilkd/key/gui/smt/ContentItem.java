// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;

import java.awt.Component;

import javax.swing.table.DefaultTableModel;


public class ContentItem {
    private String title;
    private Component component;
    private DefaultTableModel model;
    
    public String toString(){
	return title;
    }
    public ContentItem(String title) {
        super();
        this.title = title;
    }
    
    public ContentItem(String title,Component component){
	this(title);
	this.component = component;
    }
    
    public ContentItem(String title, DefaultTableModel model){
	this(title);
	this.model = model;
    }
    
    public void init(){
	if(model!= null)
	for(int i=0; i < model.getRowCount(); i++){
	    Object o = model.getValueAt(i,0);
	    if(o instanceof TableComponent){
		((TableComponent)o).prepare();
	    }
	}
    }
    
    public Component getComponent(){
	return component;
    }
    
    public DefaultTableModel getModel(){
	return model;
    }
    

}
