// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.AbstractCellEditor;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTable;
import javax.swing.JTree;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;

public class SMTSettingsDialog {
    public final static SMTSettingsDialog INSTANCE = new SMTSettingsDialog();
    public final static Component EMPTY_LINE = createSeperator();

    Settings settings;

    public void showDialog(Settings set) {
	this.settings = set;

	init();
	getJDialog().setModal(true);
	getJDialog().setVisible(true);
	

    }

    void init(DefaultMutableTreeNode node) {
	for (int i = 0; i < node.getChildCount(); i++) {
	    init((DefaultMutableTreeNode) node.getChildAt(i));
	}
	if (node.getUserObject() instanceof ContentItem) {
	    ((ContentItem) node.getUserObject()).init();
	}
    }

    private JDialog jDialog = null; // @jve:decl-index=0:visual-constraint="123,23"
    private JPanel jContentPane = null;
    private JSplitPane splitPane = null;
    private JTree optionTree = null;
    private JScrollPane jScrollPane = null;
    private JScrollPane jScrollPane1 = null;
    private OptionTable optionTable = null; // @jve:decl-index=0:visual-constraint="885,171"
    private JPanel panel = null;

    private JButton okButton = null;
    private JButton cancelButton = null;

    /**
     * This method initializes jDialog
     * 
     * @return javax.swing.JDialog
     */
    private JDialog getJDialog() {

	if (jDialog == null) {
	    jDialog = new JDialog();

	    int left = getOptionTree().getPreferredSize().width, right = 600, height = getOptionTable()
		    .getPreferredScrollableViewportSize().height;

	    jDialog.setSize(new Dimension(left + right, (int) (1.25 * height)));
	    jDialog.setTitle("SMT Solver Settings");
	    jDialog.setContentPane(getJContentPane());
	    jDialog.setLocationByPlatform(true);
	    getSplitPane().setDividerLocation(
		    (int) (1.5 * getOptionTree().getPreferredSize().width));

	}
	return jDialog;
    }

    private static Component createSeperator() {
	JPanel label = new JPanel();
	label.setPreferredSize(new Dimension(10, 10));
	return label;
    }

    /**
     * This method initializes jContentPane
     * 
     * @return javax.swing.JPanel
     */
    private JPanel getJContentPane() {
	if (jContentPane == null) {
	    jContentPane = new JPanel();
	    jContentPane.setLayout(new BorderLayout());
	    jContentPane.add(getPanel(), BorderLayout.CENTER);
	}
	return jContentPane;
    }

    /**
     * This method initializes splitPane
     * 
     * @return javax.swing.JSplitPane
     */
    private JSplitPane getSplitPane() {
	if (splitPane == null) {
	    splitPane = new JSplitPane();
	    splitPane.setLeftComponent(getJScrollPane());
	    splitPane.setRightComponent(getJScrollPane1());
	}
	return splitPane;
    }

    /**
     * This method initializes optionTree
     * 
     * @return javax.swing.JTree
     */
    private JTree getOptionTree() {
	if (optionTree == null) {
	    optionTree = new JTree();
	    optionTree.addMouseListener(new MouseAdapter() {
		@Override
		public void mouseClicked(MouseEvent e) {
		    TreePath path = optionTree.getPathForLocation(e.getX(), e
			    .getY());
		    if (path != null) {
			Object o = path.getLastPathComponent();
			if (o != null) {
			    o = ((DefaultMutableTreeNode) o).getUserObject();
			    if (o instanceof ContentItem) {
				viewOptions((ContentItem) o);

			    }
			}
		    }
		}
	    });
	}
	return optionTree;
    }

    /**
     * This method initializes saveToFilePanel
     * 
     * @return javax.swing.JPanel
     */

    /**
     * This method initializes jScrollPane
     * 
     * @return javax.swing.JScrollPane
     */
    private JScrollPane getJScrollPane() {
	if (jScrollPane == null) {
	    jScrollPane = new JScrollPane();
	    jScrollPane.setViewportView(getOptionTree());
	}
	return jScrollPane;
    }

    /**
     * This method initializes jScrollPane1
     * 
     * @return javax.swing.JScrollPane
     */
    JScrollPane getJScrollPane1() {
	if (jScrollPane1 == null) {
	    jScrollPane1 = new JScrollPane();
	}
	return jScrollPane1;
    }

    private abstract static class CellEditor extends AbstractCellEditor
	    implements TableCellEditor {

	/**
             * 
             */
	private static final long serialVersionUID = 1L;

    }

    OptionTable getOptionTable() {
	if (optionTable == null) {
	    optionTable = new OptionTable();
	    
	    optionTable.setBackground(getPanel().getBackground());


	}
	return optionTable;
    }

    /**
     * This method initializes panel
     * 
     * @return javax.swing.JPanel
     */
    private JPanel getPanel() {
	if (panel == null) {
	    GridBagConstraints gridBagConstraints11 = new GridBagConstraints();
	    gridBagConstraints11.gridx = 2;
	    gridBagConstraints11.insets = new Insets(0, 5, 5, 5);
	    gridBagConstraints11.anchor = GridBagConstraints.SOUTHEAST;
	    gridBagConstraints11.weightx = 0.0;
	    gridBagConstraints11.gridy = 1;
	    GridBagConstraints gridBagConstraints9 = new GridBagConstraints();
	    gridBagConstraints9.fill = GridBagConstraints.BOTH;
	    gridBagConstraints9.gridy = 0;
	    gridBagConstraints9.weightx = 1.0;
	    gridBagConstraints9.weighty = 1.0;
	    gridBagConstraints9.gridwidth = 3;
	    gridBagConstraints9.insets = new Insets(0, 0, 5, 0);
	    gridBagConstraints9.gridx = 0;
	    GridBagConstraints gridBagConstraints8 = new GridBagConstraints();
	    gridBagConstraints8.gridx = 0;
	    gridBagConstraints8.anchor = GridBagConstraints.SOUTHEAST;
	    gridBagConstraints8.weightx = 1.0;
	    gridBagConstraints8.insets = new Insets(0, 0, 5, 0);
	    gridBagConstraints8.gridy = 1;
	    panel = new JPanel();
	    panel.setLayout(new GridBagLayout());
	    panel.add(getOkButton(), gridBagConstraints8);
	    panel.add(getSplitPane(), gridBagConstraints9);
	    panel.add(getCancelButton(), gridBagConstraints11);
	}
	return panel;
    }


    /**
     * This method initializes okButton
     * 
     * @return javax.swing.JButton
     */
    private JButton getOkButton() {
	if (okButton == null) {
	    okButton = new JButton();
	    okButton.setText("OK");
	    okButton.addActionListener(new ActionListener() {

		public void actionPerformed(ActionEvent e) {
		    getJDialog().setVisible(false);
		    applyChanges();
		}
	    });
	}
	return okButton;
    }

    private void applyChanges() {
	settings.applyChanges();

    }

    /**
     * This method initializes cancelButton
     * 
     * @return javax.swing.JButton
     */
    private JButton getCancelButton() {
	if (cancelButton == null) {
	    cancelButton = new JButton();
	    cancelButton.setText("Cancel");
	    cancelButton.addActionListener(new ActionListener() {

		public void actionPerformed(ActionEvent arg0) {
		    getJDialog().setVisible(false);
		}
	    });
	}
	return cancelButton;
    }

    private int getRow(DefaultTableModel model, TableComponent component) {
	for (int i = 0; i < model.getRowCount(); i++) {
	    TableComponent comp = ((TableComponent) model.getValueAt(i, 2));
	    if (comp == component) {
		return i;
	    }
	}
	return -1;
    }

    void setModel(DefaultTableModel model) {
	getOptionTable().setModel(model);

	int width = 0;

	for (int i = 0; i < model.getRowCount(); i++) {
	    if (model.getValueAt(i, Settings.OPTIONCOL) instanceof TableComponent) {
		final TableComponent component = ((TableComponent) model
		        .getValueAt(i, Settings.OPTIONCOL));


		if (component.getInfo() != null && 
		    !(getOptionTable().getModel().getValueAt( i,
			    Settings.OPTIONCOL + 1) instanceof TableInfoButton)) {
		    
		    TableInfoButton button = new TableInfoButton(model,
			    component) {

			@Override
			public void eventChange() {
			    boolean change = isSelected() != isShowingInfo();

			    this.setShowInfo(this.isSelected());
			    DefaultTableModel m = (DefaultTableModel) getUserObject();
			    if (change) {
				int row = getRow(m, this);
				if (isShowingInfo() && row != -1) {
				    Object o[] = { Settings.seperator,
					    getExplanation(),
					    Settings.seperator };
				  //  getExplanation().getRendererComponent().setBackground(
					//    getOptionTable().getBackground());

				    m.insertRow(row + 1, o);
				    getOptionTable()
					    .setRowHeight(
					            row + 1,
					            getExplanation().getHeight());

				} else if (row != -1) {
				    m.removeRow(row + 1);
				}
			    }

			}

			public boolean prepareValues() {
			    // this.setTitle("Info");
			    this.setSelected(isShowingInfo());

			    return true;
			}

		    };
		    
		
		 
		   
		    getOptionTable().getModel().setValueAt(button, i,
			    Settings.OPTIONCOL + 1);
		}
		
		if((getOptionTable().getModel().getValueAt( i,
			    Settings.OPTIONCOL + 1) instanceof TableInfoButton)){
		    TableInfoButton button =  ((TableInfoButton)getOptionTable().getModel().getValueAt( i,Settings.OPTIONCOL + 1));
	
		    width = Math.max(button.getEditorComponent()
			    .getPreferredSize().width + 5, width);
		}


	    }

	}
	
	getOptionTable().setRowHeight();
	
	for (int i = 0; i < getOptionTable().getColumnModel().getColumnCount(); i++) {
	    if (Settings.OPTIONCOL != i) {
		int w = width;
		if (i == 0)
		    w = Settings.width[i];

		getOptionTable().getColumnModel().getColumn(i).setWidth(w);
		getOptionTable().getColumnModel().getColumn(i).setMaxWidth(w);
		getOptionTable().getColumnModel().getColumn(i).setMinWidth(w);
	    }

	}

    }
    
    void removeModel(DefaultTableModel model){
	for (int i = 0; i < model.getRowCount(); i++) {
	    if (model.getValueAt(i, Settings.OPTIONCOL+1) instanceof TableComponent) {
		
		
	    }
	}
    }

    void viewOptions(ContentItem item) {
	if (item.getModel() != null) {
	    setModel(item.getModel());
	    getJScrollPane1().setViewportView(getOptionTable());
	} else if (item.getComponent() != null) {
	    getJScrollPane1().setViewportView(item.getComponent());
	}

    }

    private void init() {
	getOptionTree().setModel(settings.getContent());
	viewOptions(settings.getDefaultItem());
	getJScrollPane1().setViewportView(getOptionTable());

    }
    
    class OptionTable extends JTable{
        private static final long serialVersionUID = 1L;
	DefaultTableCellRenderer renderer; 
	TableCellEditor editor;
	
	public OptionTable() {
	    setShowGrid(false);
	    setTableHeader(null);
	    renderer = new DefaultTableCellRenderer() {
		private static final long serialVersionUID = 1L;


		@Override
		public Component getTableCellRendererComponent(
			JTable table, Object value, boolean isSelected,
			boolean hasFocus, int row, int column) {

		    if (!(value instanceof TableComponent)) {
			return (Component) value;
		    }
		    // ((TableComponent) value).eventChange();

		    setToolTipText("This is a tooltip");
	
		    ((TableComponent) value).setParent(table);
		    if (((TableComponent) value).prepareValues()) {
			return ((TableComponent) value)
			.getRendererComponent();
		    } else {
			return EMPTY_LINE;
		    }
		}
	    };

	    editor = new CellEditor() {
		private static final long serialVersionUID = 1L;
		TableComponent currentValue = null;

		public Object getCellEditorValue() {

		    return currentValue;
		}

		public Component getTableCellEditorComponent(JTable table,
			Object value, boolean isSelected, int row,
			int column) {

		    if (!(value instanceof TableComponent)) {
			return null;
		    }

		    currentValue = (TableComponent) value;
		    // ((TableComponent) value).eventChange();
		    currentValue.setParent(table);
		    if (currentValue.prepare()) {
			return currentValue.getEditorComponent();
		    } else {
			return EMPTY_LINE;
		    }
		}

	    };
	    
	    
	    addComponentListener(new ComponentListener() {
	        
	        
	        
	        public void componentResized(ComponentEvent e) {
	         	setRowHeight();
	        
	        }
	        
	        public void componentMoved(ComponentEvent e) {}	        
	        public void componentHidden(ComponentEvent e) {}
	        public void componentShown(ComponentEvent e) {}
	    });


	};
	@Override
	public TableCellRenderer getCellRenderer(int row, int column) {
	    return renderer;
	}

	@Override
	public TableCellEditor getCellEditor(int row, int column) {
	    return editor;
	}
	
	private int getHeight(Object o){
	    if(o instanceof TableComponent){
		TableComponent comp = ((TableComponent)o);
		return comp.visible() ? comp.getHeight():0;
	    }
	    if(o instanceof Component){
		return ((Component)o).getPreferredSize().height;
	    }
	    return 0;
	}
	
	public void setRowHeight(){
	    for (int row = 0; row < getModel().getRowCount(); row++){
		int height =0;
		for(int col =0; col < getModel().getColumnCount(); col++){
		   Object obj = getValueAt(row, col);
		   height = Math.max(height, getHeight(obj));    
		}	
		setRowHeight(row,height);
	    }
	}
	
	

    }

}
