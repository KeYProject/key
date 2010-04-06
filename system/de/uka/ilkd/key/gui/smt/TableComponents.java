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

import javax.swing.BorderFactory;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.table.DefaultTableModel;

interface TableComponent {
    int getHeight();

    Component getRendererComponent();

    Component getEditorComponent();

    boolean prepare();

    public boolean prepareValues();

    void eventChange();

    String getInfo();

    void setShowInfo(boolean b);

    boolean isShowingInfo();

}

abstract class AbstractTableComponent<T> implements TableComponent {

    protected final int R = 0;
    protected final int E = 1;
    protected final int COUNT = 2;
    protected Object userObject;
    private boolean showInfo = false;

    AbstractTableComponent(Object userObject) {
	this.userObject = userObject;
    }

    AbstractTableComponent() {
	this(null);
    }

    public Component getEditorComponent() {
	return (Component) getComp(E);
    }

    public int getHeight() {
	if (((Component) getComp(E)) == null) {
	    return 10;
	}
	return ((Component) getComp(E)).getPreferredSize().height;
    }

    public Component getRendererComponent() {
	return (Component) getComp(R);
    }

    public Object getUserObject() {
	return userObject;
    }

    abstract T getComp(int i);

    public boolean prepare() {
	return prepareValues();
    }

    public String getInfo() {
	return null;
    }

    public void setShowInfo(boolean b) {
	showInfo = b;
    }

    public boolean isShowingInfo() {
	return showInfo;
    }

}

abstract class TableCheckBox extends AbstractTableComponent<JCheckBox> {
    private JCheckBox comp[] = { new JCheckBox(), new JCheckBox() };
    private ActionListener listener = new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	    eventChange();
	}
    };

    public JCheckBox getComp(int i) {
	return comp[i];
    }

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

    public boolean prepare() {
	return prepareValues();
    }

    public abstract void eventChange();

    TableCheckBox(Object userObject) {
	super(userObject);
	comp[E].addActionListener(listener);
    }

    TableCheckBox() {
	this(null);
    }

}

abstract class TableSaveToFile extends AbstractTableComponent<SaveToFilePanel> {
    private SaveToFilePanel comp[] = { new SaveToFilePanel(),
	    new SaveToFilePanel() };

    private ActionListener actionListener = new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	    eventChange();
	}
    };

    private DocumentListener documentListener = new DocumentListener() {

	public void changedUpdate(DocumentEvent e) {
	    eventChange();

	}

	public void insertUpdate(DocumentEvent e) {
	    eventChange();

	}

	public void removeUpdate(DocumentEvent e) {
	    eventChange();

	}

    };

    public TableSaveToFile() {
	comp[E].getSaveToFileBox().addActionListener(actionListener);
	comp[E].getFolderField().getDocument().addDocumentListener(
	        documentListener);
    }

    public boolean prepare() {

	return prepareValues();

    }

    public SaveToFilePanel getComp(int i) {
	return comp[i];
    }

    protected void enable(boolean b) {
	for (int i = 0; i < 2; i++) {
	    comp[i].getChooseButton().setEnabled(b);
	    comp[i].getFolderField().setEnabled(b);
	    comp[i].getSaveToFileExplanation().setEnabled(b);
	}
    }

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
	//enable(b);
    }

    public void setFolder(String text) {
	for (int i = 0; i < 2; i++) {
	    comp[i].getFolderField().setText(text);
	}
    }

    public boolean isActivated() {
	return comp[E].getSaveToFileBox().isSelected();
    }

    public String getFolder() {
	return comp[E].getFolderField().getText();
    }

}

abstract class TableSlider extends AbstractTableComponent<JSlider> {
    private JSlider[] comp = { new JSlider(), new JSlider() };

    public JSlider getComp(int i) {
	return comp[i];
    }

    public void setTitle(String title) {
	/*
	 * for(int i=0; i < 2; i ++){
	 * comp[i].setBorder(BorderFactory.createTitledBorder(null, title ,
	 * TitledBorder.DEFAULT_JUSTIFICATION , TitledBorder.DEFAULT_POSITION,
	 * null, null)); }
	 */
    }

    public void clean() {
    };

    public void setTimeout(int timeout) {

    }

    public int getTimeout() {
	return 0;
    }

}

abstract class TableComboBox extends AbstractTableComponent<JComboBox> {
    private JComboBox[] comp = { new JComboBox(), new JComboBox() };
    ActionListener listener = new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	    eventChange();
	}
    };

    public JComboBox getComp(int i) {
	return comp[i];
    }

    public void setItems(Object... items) {

	for (JComboBox box : comp) {
	    box.removeAllItems();
	    for (Object o : items) {
		box.addItem(o);
	    }

	}
    }

    public TableComboBox(int selected,Object... items) {
	comp[E].addActionListener(listener);
	setItems(items);
	setSelectedItem(selected);
    }

    public boolean prepare() {
	return prepareValues();
    }

    public int getSelectedItemIndex() {
	return comp[E].getSelectedIndex();
    }

    public void setSelectedItem(int index) {
	for (JComboBox box : comp) {
	    box.setSelectedIndex(index);
	}
    }
}

abstract class TableProperty extends AbstractTableComponent<PropertyPanel> {
    private PropertyPanel comp[] = { new PropertyPanel(), new PropertyPanel() };

    private DocumentListener documentListener = new DocumentListener() {

	public void changedUpdate(DocumentEvent e) {
	    eventChange();

	}

	public void insertUpdate(DocumentEvent e) {
	    eventChange();

	}

	public void removeUpdate(DocumentEvent e) {
	    eventChange();

	}

    };

    public PropertyPanel getComp(int i) {
	return comp[i];
    }

    public TableProperty(Object userObject) {
	this.userObject = userObject;
	comp[E].valueField.getDocument().addDocumentListener(documentListener);
	
    }

    public String getValue() {
	return comp[E].valueField.getText();
    }

    public boolean prepare() {
	return prepareValues();
    }

    protected void setTitle(String title) {
	for (int i = 0; i < 2; i++) {
	    comp[i].propertyLabel.setText(title);
	}
    }

    protected void setEditable(boolean editable) {
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

abstract class TableInfoButton extends AbstractTableComponent<InfoPanel> {
    private InfoPanel comp[] = { new InfoPanel(), new InfoPanel() };
    private TableExplanation textArea = new TableExplanation();
    private ActionListener listener = new ActionListener() {
	public void actionPerformed(ActionEvent e) {
	    eventChange();
	}
    };

    public InfoPanel getComp(int i) {
	return comp[i];
    }

    public void setSelected(boolean b) {
	for (int i = 0; i < COUNT; i++) {
	    comp[i].setSelected(b);
	}

    }

    public void setTitle(String title) {
	for (int i = 0; i < COUNT; i++) {
	    comp[i].getToogleButton().setText(title);
	}

    }

    public boolean isSelected() {
	return comp[E].isSelected();
    }

    public boolean prepare() {
	return prepareValues();
    }

    @Override
    public int getHeight() {
	return comp[E].getToogleButton().getPreferredSize().height + 5;
    }

    public TableComponent getExplanation() {
	if (client.getInfo() != null) {
	    textArea.init(client.getInfo());
	}
	return textArea;
    }

    public TableComponent getClient() {
	return client;
    }
    
      public abstract void eventChange();

    private TableComponent client;

    TableInfoButton(DefaultTableModel model, TableComponent client) {
	super(model);

	comp[E].getToogleButton().addActionListener(listener);
	this.client = client;
    }

}

class TableExplanation extends AbstractTableComponent<JTextArea>{
    JTextArea textArea = new JTextArea();
    
    void init(String text){
	    textArea.setText(text);
	    textArea.setRows(textArea.getLineCount() + 1);
    }
    
 
    @Override
    public int getHeight() {
	return textArea.getPreferredSize().height;
    }
    
    @Override
    JTextArea getComp(int i) {
	
	return i==R? textArea : null;
    }
    public void eventChange() {
    }
    public boolean prepareValues() {
	return true;
    }
    
}

class TableSeperator extends AbstractTableComponent<JPanel> {
    private static JPanel comp[] = { createSeperator(), createSeperator() };

    public JPanel getComp(int i) {
	return comp[i];
    }

    public void eventChange() {
    }

    public boolean prepare() {
	return true;
    }

    @Override
    public int getHeight() {
	return 10;
    }

    private static JPanel createSeperator() {
	JPanel label = new JPanel();
	label.setPreferredSize(new Dimension(10, 10));
	return label;
    }

    public boolean prepareValues() {

	return true;
    }

    public void clean() {

    }

}
