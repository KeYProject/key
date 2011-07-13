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

import javax.swing.table.DefaultTableModel;
import javax.swing.tree.DefaultTreeModel;


 

public abstract class Settings {
    abstract public DefaultTreeModel    getContent();
    public abstract void applyChanges();
    public abstract ContentItem getDefaultItem();
    public final static int OPTIONCOL=1; 
    public final static int width []= {10,-1,30};
    public final static TableSeperator seperator = new TableSeperator();
    
    protected DefaultTableModel buildModel(String title, Object[] data) {
	DefaultTableModel model = new DefaultTableModel();

	model = new DefaultTableModel();
	model.addColumn("");
	model.addColumn(title);
	model.addColumn("");

	
	
	Object[] sep = {seperator,seperator,seperator};
	model.addRow(sep);
	for (int i = 0; i < data.length; i++) {
	    Object[] dat = {sep[0], data[i],sep[0] };
	    model.addRow(dat);
	    model.addRow(sep);

	}
	


	return model;
    }
    
    
	
    
}
