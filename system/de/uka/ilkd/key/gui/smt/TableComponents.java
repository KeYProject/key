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
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.BorderFactory;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

interface TableComponent {
    int getHeight();

    Component getRendererComponent();

    Component getEditorComponent();

    boolean prepare();

    void eventChange();

}

abstract class AbstractTableComponent<T> implements TableComponent {

    protected final int R = 0;
    protected final int E = 1;
    protected final int COUNT = 2;
    protected Object userObject;

    protected T comp[];

    protected void set(T renderer, T editor) {
	comp[R] = renderer;
	comp[E] = editor;
    }
    
    AbstractTableComponent(Object userObject){
	this.userObject = userObject;
    }
    
    AbstractTableComponent(){
	this(null);
    }

    public Component getEditorComponent() {
	return (Component) comp[E];
    }

    public int getHeight() {
	return ((Component) comp[R]).getPreferredSize().height;
    }

    public Component getRendererComponent() {
	return (Component) comp[R];
    }
    
    public Object getUserObject(){
	return userObject;
    }
}

abstract class TableCheckBox extends AbstractTableComponent<JCheckBox> {

    
    public void setSelected(boolean b) {
	for (int i = 0; i < COUNT; i++) {
	    comp[i].setSelected(b);
	}
    }

    public void setTitle(String title) {
	for (int i = 0; i < COUNT; i++) {
	    comp[i].setText(title);
	}
    }

    public boolean isSelected() {
	return comp[E].isSelected();
    }

    public abstract void eventChange();
    
    TableCheckBox(Object userObject){
	super(userObject);
	comp = new JCheckBox[2];
	set(new JCheckBox(), new JCheckBox());
	comp[E].addActionListener(new ActionListener() {

	    public void actionPerformed(ActionEvent arg0) {
		 eventChange();
	    }
	});

    }

    TableCheckBox() {
	this(null);
    }

}

abstract class TableSaveToFile extends AbstractTableComponent<SaveToFilePanel> {

    private String title;
    
    public TableSaveToFile(String title) {
	this.title = title;
        comp = new SaveToFilePanel[2];
	set(new SaveToFilePanel(), new SaveToFilePanel());
	comp[E].getSaveToFileBox().addActionListener(new ActionListener() {
	    
	    public void actionPerformed(ActionEvent e) {
	
		eventChange();
		
 
		
	    }
	});

	comp[E].getFolderField().getDocument().addDocumentListener(new DocumentListener(){

	    public void changedUpdate(DocumentEvent e) {
	        eventChange();
	        
            }

	    public void insertUpdate(DocumentEvent e) {
	        eventChange();
	        
            }

	    public void removeUpdate(DocumentEvent e) {
	        eventChange();
	        
            }
	    
	});
	
	

	
    }
    
    protected void enable(boolean b){
	for (int i = 0; i < 2; i++) {	    
	    comp[i].getChooseButton().setEnabled(b);
	    comp[i].getFolderField().setEnabled(b);
	    comp[i].getSaveToFileExplanation().setEnabled(b);
	}
    }
    
    public boolean prepare() {
	setTitle(title);
	return prepareProperties();
    }
    
    abstract protected boolean prepareProperties();

    public void setTitle(String title) {
	for (int i = 0; i < 2; i++) {
	    comp[i].setBorder(BorderFactory.createTitledBorder(null, title,
		    TitledBorder.DEFAULT_JUSTIFICATION,
		    TitledBorder.DEFAULT_POSITION, null, null));
	}
    }

    public void setActivated(boolean b) {
	for (int i = 0; i < 2; i++) {
	    comp[i].getSaveToFileBox().setSelected(b);
	}
    }

    public void setFolder(String text) {
	for (int i = 0; i < 2; i++) {
	    comp[i].getFolderField().setText(text);
	}
    }
    
    public boolean isActivated(){
	return comp[E].getSaveToFileBox().isSelected();
    }
    
    public String getFolder(){
	return comp[E].getFolderField().getText();
    }

}

abstract class TableSlider extends AbstractTableComponent<JSlider> {

    public TableSlider() {
	comp = new JSlider[2];
	set(new JSlider(), new JSlider());
	

    }

    public void setTitle(String title) {
	/*
	 * for(int i=0; i < 2; i ++){
	 * comp[i].setBorder(BorderFactory.createTitledBorder(null, title ,
	 * TitledBorder.DEFAULT_JUSTIFICATION , TitledBorder.DEFAULT_POSITION,
	 * null, null)); }
	 */
    }

    public void setTimeout(int timeout) {

    }

    public int getTimeout() {
	return 0;
    }

}

abstract class TableComboBox extends AbstractTableComponent<JComboBox> {
    public TableComboBox() {
	comp = new JComboBox[2];
	set(new JComboBox(), new JComboBox());

	comp[E].addActionListener(new ActionListener() {

	    public void actionPerformed(ActionEvent e) {
		//comp[R].setSelectedItem(comp[E].getSelectedItem());
		eventChange();
	    }
	});

    }

    public void setItems(Object... items) {
	for (JComboBox box : comp) {
	    box.removeAllItems();
	    for (Object o : items) {
		box.addItem(o);
	    }

	}
    }

    public Object getSelectedItem() {
	return comp[E].getSelectedItem();
    }
    
    public void setSelectedItem(Object o){
	for(JComboBox box : comp){
	    box.setSelectedItem(o);
	}
    }
}

class TableProperty extends AbstractTableComponent<PropertyPanel> {

    
    private String name;
    private boolean editable;

    private Object value;

    public TableProperty(String name, Object value, Object userObject) {
	this(name, value,userObject, true);
    }

    public TableProperty(String name, Object value,Object userObject,  boolean enabled) {
	comp = new PropertyPanel[2];
	this.value = value;
	this.name = name;
	this.editable = enabled;
	this.userObject = userObject;
	set(new PropertyPanel(), new PropertyPanel());
	comp[E].getValueField().getDocument().addDocumentListener(new DocumentListener(){

	    public void changedUpdate(DocumentEvent e) {
	        eventChange();
	        
            }

	    public void insertUpdate(DocumentEvent e) {
	        eventChange();
	        
            }

	    public void removeUpdate(DocumentEvent e) {
	        eventChange();
	        
            }
	    
	});

    }
    
    public String getValue(){
	return comp[E].valueField.getText();
    }

   
    protected boolean prepareProperty(){
	return true;
    }
    
    public boolean prepare() {
	setTitle(name);
	setValue(value);
	setEditable(editable);
	return  prepareProperty();
    }
    

    public void eventChange() {
        // TODO Auto-generated method stub
        
    }

    private void setTitle(String title) {
	for (int i = 0; i < 2; i++) {
	    comp[i].propertyLabel.setText(title);
	}
    }

    private void setEditable(boolean editable) {
	for (int i = 0; i < 2; i++) {
	    comp[i].valueField.setEditable(editable);
	}
    }

    protected void setValue(Object value) {
	for (int i = 0; i < 2; i++) {
	    comp[i].getValueField().setText(value.toString());
	}
    }

}

class TableSeperator extends AbstractTableComponent<JPanel> {
    public void eventChange() {
    }

    public boolean prepare() {
	return true;
    }

    public TableSeperator() {
	comp = new JPanel[2];
	set(createSeperator(), createSeperator());

    }

    private static JPanel createSeperator() {
	JPanel label = new JPanel();
	label.setPreferredSize(new Dimension(10, 10));
	return label;
    }

}
