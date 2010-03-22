package de.uka.ilkd.key.gui.smt;


import javax.swing.JDialog;
import javax.swing.JPanel;
import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import javax.swing.JSplitPane;
import javax.swing.JTree;
import java.awt.GridBagLayout;
import javax.swing.BorderFactory;
import javax.swing.border.TitledBorder;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableCellEditor;
import javax.swing.table.TableCellRenderer;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;

import java.awt.GridBagConstraints;
import javax.swing.JCheckBox;
import javax.swing.JTextField;
import javax.swing.JOptionPane;
import javax.swing.JButton;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.AbstractCellEditor;
import javax.swing.DefaultCellEditor;
import javax.swing.JTextArea;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JSlider;
import javax.swing.JLabel;


interface TableComponent{
	int getHeight();
	Component getRendererComponent();
	Component getEditorComponent();
	boolean prepare();
	void eventChange();
	
	
}

abstract class AbstractTableComponent<T> implements TableComponent{
   
    protected final int R =0;
    protected final int E   =1;
    protected final int COUNT = 2;
    protected T comp[] ;

  
    

    
    protected void set(T renderer, T editor){
	comp[R] = renderer;
	comp[E] = editor;
    }

    public Component getEditorComponent() {
	return (Component) comp[E];
    }

    public int getHeight() {
	return ((Component)comp[R]).getPreferredSize().height;
    }

    public Component getRendererComponent() {
	return (Component)comp[R];
    }
}

abstract class TableCheckBox extends AbstractTableComponent<JCheckBox>{
	
	public void setSelected(boolean b){
	    for(int i=0; i < COUNT; i ++){
		comp[i].setSelected(b);
	    }
	}
	
	public void setTitle(String title){
	    for(int i=0; i < COUNT; i ++){
		comp[i].setText(title);
	    }    
	}
	
	public boolean isSelected(){
	    return comp[E].isSelected();
	}
	
	public abstract void eventChange();
	
	TableCheckBox(){
	    	comp = new JCheckBox[2];
	    	set(new JCheckBox(),new JCheckBox());
	        comp[E].addActionListener(new ActionListener() {
	        
	        public void actionPerformed(ActionEvent arg0) {
	         //   eventChange();
	        }
	    });
	}
	
	
}
	 


abstract class TableSaveToFile extends AbstractTableComponent<SaveToFilePanel>{
  
   
    
    
    public TableSaveToFile() {
	comp = new SaveToFilePanel[2];
	set(new SaveToFilePanel(),new SaveToFilePanel());
	
    }
    
    public void setTitle(String title){
	for(int i=0; i < 2; i ++){
	    comp[i].setBorder(BorderFactory.createTitledBorder(null, title
		    , TitledBorder.DEFAULT_JUSTIFICATION
		    , TitledBorder.DEFAULT_POSITION, null, null));
	}
    }
    
    public void setActivated(boolean b){
	for(int i=0; i < 2; i ++){
	    comp[i].getSaveToFileBox().setSelected(b);
	}
    }
    
    public void setFolder(String text){
	for(int i=0; i < 2; i ++){
	    comp[i].getFolderField().setText(text);
	}
    }
    

    
       
}

abstract class TableSlider extends AbstractTableComponent<SliderPanel>{
  
   
    
    
    public TableSlider() {
	comp = new SliderPanel[2];
	set(new SliderPanel(),new SliderPanel());
	
    }
    
    public void setTitle(String title){
	for(int i=0; i < 2; i ++){
	    comp[i].setBorder(BorderFactory.createTitledBorder(null, title
		    , TitledBorder.DEFAULT_JUSTIFICATION
		    , TitledBorder.DEFAULT_POSITION, null, null));
	}
    }
    
    public void setTimeout(int timeout){
	
    }
    
    public int getTimeout(){
	return 0;
    }
    

    

    

    
       
}

abstract class TableProperty extends AbstractTableComponent<PropertyPanel>{
    public TableProperty() {
	comp = new PropertyPanel[2];
	set(new PropertyPanel(),new PropertyPanel());
	comp[E].getValueField().addKeyListener(new KeyAdapter() {
	    @Override
	    public void keyTyped(KeyEvent e) {
		comp[R].getValueField().setText(comp[E].getValueField().getText());
	    }
	});
	
    }
    
    public void setTitle(String title){
	for(int i=0; i < 2; i ++){
	   comp[i].propertyLabel.setText(title);
	}
    }
    
    public void setValue(String value){
	for(int i=0; i < 2; i ++){
	   comp[i].getValueField().setText(value);
	}
    }
    
}

class TableSeperator extends AbstractTableComponent<JPanel>{
    public void eventChange() {
    }
    public boolean prepare() {
	return true;
    }
    
    public TableSeperator() {
	comp = new JPanel[2];
	set(createSeperator(),createSeperator());
	
    }
    
    private static  JPanel createSeperator(){
		JPanel label = new JPanel();
		label.setPreferredSize(new Dimension(10,10));
		return label;
	}
    
    
    
}

class PropertyPanel extends JPanel {
    JLabel propertyLabel = null;
    JTextField valueField = null;

    public PropertyPanel() {

	GridBagConstraints gridBagConstraints13 = new GridBagConstraints();
	gridBagConstraints13.fill = GridBagConstraints.BOTH;
	gridBagConstraints13.gridy = 0;
	gridBagConstraints13.weightx = 0.7;
	gridBagConstraints13.anchor = GridBagConstraints.NORTHEAST;
	gridBagConstraints13.weighty = 1.0;
	gridBagConstraints13.gridx = 1;
	GridBagConstraints gridBagConstraints12 = new GridBagConstraints();
	gridBagConstraints12.gridx = 0;
	gridBagConstraints12.anchor = GridBagConstraints.WEST;
	gridBagConstraints12.weightx = 0.3;
	gridBagConstraints12.weighty = 1.0;
	gridBagConstraints12.gridy = 0;
	gridBagConstraints12.insets = new Insets(0,5,0,0); 
	propertyLabel = new JLabel();
	propertyLabel.setText("Property Name");
	setLayout(new GridBagLayout());
	setSize(new Dimension(289, 23));
	add(propertyLabel, gridBagConstraints12);
	add(getValueField(), gridBagConstraints13);

    }

    /**
     * This method initializes valueField
     * 
     * @return javax.swing.JTextField
     */
    public JTextField getValueField() {
	if (valueField == null) {
	    valueField = new JTextField();
	}
	return valueField;
    }
}

class SliderPanel extends JPanel{
    	private JSlider slider = null;
    	public SliderPanel() {
		 GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
		 gridBagConstraints7.fill = GridBagConstraints.BOTH;
		 gridBagConstraints7.gridy = 0;
			gridBagConstraints7.weightx = 1.0;
			gridBagConstraints7.weighty = 1.0;
			gridBagConstraints7.insets = new Insets(5, 0, 5, 0);
			gridBagConstraints7.gridx = 0;
			
			setLayout(new GridBagLayout());
			setSize(new Dimension(397, 68));
			setBorder(BorderFactory.createTitledBorder(null, "Timeout:",
				TitledBorder.DEFAULT_JUSTIFICATION,
				TitledBorder.DEFAULT_POSITION, null, null));
			add(getTimeoutSlider(), gridBagConstraints7);
	
		
	}


	private JSlider getTimeoutSlider() {
		slider = new JSlider();
		
		slider = new JSlider();
		slider.setPaintLabels(true);
		
		return slider;
	}
}


class SaveToFilePanel extends JPanel{
	private JCheckBox saveToFileBox = null;
	private JTextField folderField = null;
	private JButton chooseButton = null;
	private JTextArea saveToFileExplanation = null;
	

	
	
	public SaveToFilePanel() {

	    GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
	    gridBagConstraints3.fill = GridBagConstraints.BOTH;
	    gridBagConstraints3.gridy = 1;
	    gridBagConstraints3.weightx = 1.0;
	    gridBagConstraints3.weighty = 1.0;
	    gridBagConstraints3.gridwidth = 2;
	    gridBagConstraints3.ipady = 34;
	    gridBagConstraints3.anchor = GridBagConstraints.CENTER;
	    gridBagConstraints3.insets = new Insets(5, 0, 2, 0);
	    gridBagConstraints3.gridx = 0;
	    GridBagConstraints gridBagConstraints = new GridBagConstraints();
	    gridBagConstraints.gridx = 1;
	    gridBagConstraints.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints.weightx = 0.1;
	    gridBagConstraints.insets = new Insets(0, 6, 0, 0);
	    gridBagConstraints.gridy = 0;
	    GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
	    gridBagConstraints2.fill = GridBagConstraints.BOTH;
	    gridBagConstraints2.gridy = 0;
	    gridBagConstraints2.weightx = 0.5;
	    gridBagConstraints2.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints2.ipadx = 100;
	    gridBagConstraints2.gridx = 0;
	    GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
	    gridBagConstraints1.gridx = 0;
	    gridBagConstraints1.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints1.fill = GridBagConstraints.HORIZONTAL;
	    gridBagConstraints1.weightx = 1.0;
	    gridBagConstraints1.gridy = 2;

	    setLayout(new GridBagLayout());
	    setBorder(BorderFactory.createTitledBorder(null, "Save translated problem to file:",
		    TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, null));
	    setSize(new Dimension(456, 129));
	    add(getSaveToFileBox(), gridBagConstraints1);
	    add(getFolderField(), gridBagConstraints2);
	    add(getChooseButton(), gridBagConstraints);
	    add(getSaveToFileExplanation(), gridBagConstraints3);
	    getSaveToFileExplanation().setEditable(false);
	    getSaveToFileExplanation().setBackground(this.getBackground());
	    getSaveToFileBox().addActionListener(new ActionListener() {
	        
	        public void actionPerformed(ActionEvent arg0) {
	    		boolean b = getSaveToFileBox().isSelected();
	    		
	    		getChooseButton().setEnabled(b);
	    		getFolderField().setEnabled(b);
	    		getSaveToFileExplanation().setEnabled(b);
	    		
	    	
	        }
	    });


	}

	/**
	 * This method initializes saveToFileBox	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	public JCheckBox getSaveToFileBox() {
		if (saveToFileBox == null) {
			saveToFileBox = new JCheckBox();
			saveToFileBox.setText("activated");
		}
		return saveToFileBox;
	}

	/**
	 * This method initializes folderField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	public JTextField getFolderField() {
		if (folderField == null) {
			folderField = new JTextField();
		}
		return folderField;
	}

	/**
	 * This method initializes chooseButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	public JButton getChooseButton() {
		if (chooseButton == null) {
			chooseButton = new JButton();
			chooseButton.setText("choose folder");
		}
		return chooseButton;
	}

	/**
	 * This method initializes saveToFileExplanation	
	 * 	
	 * @return javax.swing.JTextArea	
	 */
	public JTextArea getSaveToFileExplanation() {
		if (saveToFileExplanation == null) {
			saveToFileExplanation = new JTextArea();
			saveToFileExplanation.setLineWrap(true);
			saveToFileExplanation.setText("Explanation of this field....");
		}
		return saveToFileExplanation;
	}
}




public class DPSDialog {
    	public final static DPSDialog INSTANCE = new DPSDialog();
    	public final static Component    EMPTY_LINE = createSeperator();
    	TemporarySettings settings;
    	
    	public void showDialog(DecisionProcedureSettings set){
    	     settings = new TemporarySettings(set);
    	     getJDialog().setVisible(true);
    	}
    	

    private TableComponent[] getSolverData(){
	TableComponent data[] = {
	
		
	};
	return data;
    }
    
    private TableComponent[] getGeneralOptionsData() {
	TableComponent data[] = {

	new TableSlider() {

	    public void eventChange() {
		settings.timeout = getTimeout();

	    }

	    public boolean prepare() {
		setTitle("Timeout:");
		setTimeout(settings.timeout);
		return true;
	    }

	}

	,

	new TableCheckBox() {
	    public boolean prepare() {
		setTitle("Show results after executing solvers.");
		setSelected(settings.showResultsAfterExecuting);
		return true;
	    }

	    @Override
	    public void eventChange() {

		settings.showResultsAfterExecuting = isSelected();
	    }
	},

	new TableCheckBox() {

	    @Override
	    public void eventChange() {
		settings.useWeakenTypeSystem = isSelected();

	    }

	    public boolean prepare() {
		setTitle("Use translation of weaken type system.");
		setSelected(settings.useWeakenTypeSystem);
		return true;
	    }

	},

	new TableSaveToFile() {

	    public boolean prepare() {
		setTitle("Save translation to file:");
		setFolder(settings.folder);
		setActivated(settings.storeToFile);
		return true;
	    }

	    public void eventChange() {

	    }
	}

	};

	return data;

    }
    
    
    private TableComponent[] getTacletOptionsData() {
	TableComponent data[] = {




	new TableSaveToFile() {

	    public boolean prepare() {
		setTitle("Save taclet translation to file:");
		setFolder(settings.folder);
		setActivated(settings.storeToFile);
		return true;
	    }

	    public void eventChange() {

	    }
	},
	new TableProperty() {


	    public void eventChange() {
	

	    }

	    public boolean prepare() {
		setTitle("Maximum number of different generic sorts:");
	
		return true;
	    }

	}

	};

	return data;

    }
    
    
	
	abstract class OptionItem{
	
	    String title;
	    public String toString(){
		return title;
	    }
	    public OptionItem(String title) {
	        super();
	        this.title = title;
            }
	    
	    abstract public void eventClicked();
	    
	}
	
	
	private DefaultTreeModel getContentData(){
	    DefaultMutableTreeNode root = new DefaultMutableTreeNode();
	    root.setUserObject("Options");
	    
	    DefaultMutableTreeNode generalOptions = new DefaultMutableTreeNode();
	    generalOptions.setUserObject(new OptionItem("General"){
		@Override
                public void eventClicked() {
		    setModel(getGeneralModel(title));
		    getJScrollPane1().setViewportView(getOptionTable());
                }		
	       }
	    );
	    
	    DefaultMutableTreeNode solverOptions = new DefaultMutableTreeNode();
	    solverOptions.setUserObject("Solvers");
	    
	    DefaultMutableTreeNode tacletOptions = new DefaultMutableTreeNode();
	    tacletOptions.setUserObject(new OptionItem("Taclets"){
		@Override
                public void eventClicked() {
		    setModel(getTacletModel(title));
		    getJScrollPane1().setViewportView(getOptionTable());
                }		
	       }
	    );
	    
	    
	    root.add(generalOptions);
	    root.add(solverOptions);
	    root.add(tacletOptions);
	    
	    
	    DefaultTreeModel model = new DefaultTreeModel(root);
	    return model;  
	}

	private JDialog jDialog = null;  //  @jve:decl-index=0:visual-constraint="123,23"
	private JPanel jContentPane = null;
	private JSplitPane splitPane = null;
	private JTree optionTree = null;
	private JScrollPane jScrollPane = null;
	private JScrollPane jScrollPane1 = null;
	private JTable optionTable = null;  //  @jve:decl-index=0:visual-constraint="885,171"
	private JPanel checkBoxPanel = null;  //  @jve:decl-index=0:visual-constraint="499,156"
	private JTextArea checkBoxExplanation = null;
	private JCheckBox checkBox = null;
	private JPanel panel = null;
	private JButton applyButton = null;
	private JButton okButton = null;
	private JButton cancelButton = null;
	private JPanel propertyPanel = null;  //  @jve:decl-index=0:visual-constraint="100,245"
	private JLabel propertyLabel = null;
	private JTextField valueField = null;
	private JPanel propertyPanel2 = null;  //  @jve:decl-index=0:visual-constraint="134,345"
	private JLabel propertyLabel2 = null;
	private JTextField valueField2 = null;
	private JTextArea propertyExplanation = null;
	private DefaultTableModel generalOptionsModel = null;
	private DefaultTableModel tacletOptionsModel  = null;
	private static final Component SEPERATOR_COMP = createSeperator();
	private static final InternComponent SEPERATOR = new InternComponent(SEPERATOR_COMP, SEPERATOR_COMP);
	/**
	 * This method initializes jDialog	
	 * 	
	 * @return javax.swing.JDialog	
	 */
	private JDialog getJDialog() {
		if (jDialog == null) {
			jDialog = new JDialog();
			jDialog.setSize(new Dimension(329, 170));
			jDialog.setTitle("Decision Procedure Settings");
			jDialog.setContentPane(getJContentPane());
			init();
		}
		return jDialog;
	}
	
	private static Component createSeperator(){
		JPanel label = new JPanel();
		label.setPreferredSize(new Dimension(10,10));
		return label;
	}
	
	private static class InternComponent{
		Component renderer;
		Component editor;
		public InternComponent(Component renderer, Component editor){
			this.renderer = renderer;
			this.editor = editor;
		}
		
		int getHeight(){
			return renderer.getPreferredSize().height;
		}
	}
	
	
	private DefaultTableModel getTacletModel(String title){
	    if(tacletOptionsModel == null){
		tacletOptionsModel = buildModel(title, getTacletOptionsData());
		
	    }
	    return tacletOptionsModel;
	}
	
	private DefaultTableModel getGeneralModel(String title){
	    if(generalOptionsModel == null){
		generalOptionsModel = buildModel(title, getGeneralOptionsData());
		
	    }
	    return generalOptionsModel;
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
			   TreePath path = optionTree.getPathForLocation(e.getX(), e.getY());
			   if(path != null){
			       Object o = path.getLastPathComponent();
			       if(o!= null){
				   o = ((DefaultMutableTreeNode)o).getUserObject();
				   if(o instanceof OptionItem){
				   ((OptionItem) o).eventClicked();
				   System.out.println("hallo");
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
	private JScrollPane getJScrollPane1() {
		if (jScrollPane1 == null) {
			jScrollPane1 = new JScrollPane();
		}
		return jScrollPane1;
	}

	/**
	 * This method initializes optionTable	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private abstract static class CellEditor extends AbstractCellEditor
									implements TableCellEditor{
		
	}
	
	private JTable getOptionTable() {
	    if (optionTable == null) {
		optionTable = new JTable(){
		    DefaultTableCellRenderer renderer = new DefaultTableCellRenderer(){


			@Override
			public Component getTableCellRendererComponent(JTable table,
				Object value,
				boolean isSelected,
				boolean hasFocus,
				int row,
				int column) {
			    if(!(value instanceof TableComponent)){
				return (Component) value;
			    }
			    ((TableComponent) value).eventChange();
			    
			    setToolTipText("This is a tooltip");
			    // TODO Auto-generated method stub
			    if(((TableComponent) value).prepare()){
				return ((TableComponent) value).getRendererComponent();
			    }else{
				return EMPTY_LINE;
			    }
			}
		    };

		    TableCellEditor editor = new CellEditor(){
			Object currentValue =  null;
			public Object getCellEditorValue() {

			    return currentValue;
			}

			public Component getTableCellEditorComponent(JTable table, Object value, 
				boolean isSelected, int row, int column) {
			    if(!(value instanceof TableComponent)){
				return (Component) value;
			    }
			    currentValue = value;
			    ((TableComponent) value).eventChange();
			    if(((TableComponent) value).prepare()){
				return ((TableComponent) value).getEditorComponent();
			    }else{
				return EMPTY_LINE;
			    }
			}

		    };



		    @Override
		    public TableCellRenderer getCellRenderer(int row, int column) {

			return renderer;
			//return super.getCellRenderer(row, column);
		    }

		    @Override
		    public TableCellEditor getCellEditor(int row, int column) {

			return editor;
		    }
		};
		optionTable.setShowGrid(false);









	    }
	    return optionTable;
	}

	/**
	 * This method initializes checkBoxPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getCheckBoxPanel() {
		if (checkBoxPanel == null) {
			GridBagConstraints gridBagConstraints5 = new GridBagConstraints();
			gridBagConstraints5.gridx = 0;
			gridBagConstraints5.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints5.gridy = 1;
			GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
			gridBagConstraints4.fill = GridBagConstraints.BOTH;
			gridBagConstraints4.gridy = 0;
			gridBagConstraints4.weightx = 1.0;
			gridBagConstraints4.weighty = 1.0;
			gridBagConstraints4.gridx = 0;
			checkBoxPanel = new JPanel();
			checkBoxPanel.setLayout(new GridBagLayout());
			checkBoxPanel.setSize(new Dimension(357, 103));
			checkBoxPanel.setBorder(BorderFactory.createTitledBorder(null, "Show result dialog:", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, null));
			checkBoxPanel.add(getCheckBoxExplanation(), gridBagConstraints4);
			checkBoxPanel.add(getCheckBox(), gridBagConstraints5);
		}
		return checkBoxPanel;
	}

	/**
	 * This method initializes checkBoxExplanation	
	 * 	
	 * @return javax.swing.JTextArea	
	 */
	private JTextArea getCheckBoxExplanation() {
		if (checkBoxExplanation == null) {
			checkBoxExplanation = new JTextArea();
			checkBoxExplanation.setText("Explanation of this field....");
			checkBoxExplanation.setLineWrap(true);
		}
		return checkBoxExplanation;
	}

	/**
	 * This method initializes checkBox	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	private JCheckBox getCheckBox() {
		if (checkBox == null) {
			checkBox = new JCheckBox();
			checkBox.setText("activated");
		}
		return checkBox;
	}

	/**
	 * This method initializes timeoutPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getTimeoutPanel() {
		JPanel timeoutPanel = new JPanel();
			GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
			gridBagConstraints7.fill = GridBagConstraints.BOTH;
			gridBagConstraints7.gridy = 0;
			gridBagConstraints7.weightx = 1.0;
			gridBagConstraints7.weighty = 1.0;
			gridBagConstraints7.insets = new Insets(5, 0, 5, 0);
			gridBagConstraints7.gridx = 0;
			timeoutPanel = new JPanel();
			timeoutPanel.setLayout(new GridBagLayout());
			timeoutPanel.setSize(new Dimension(397, 68));
			timeoutPanel.setBorder(BorderFactory.createTitledBorder(null, "Timeout:", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, null));
			timeoutPanel.add(getTimeoutSlider(), gridBagConstraints7);
	
		return timeoutPanel;
	}

	/**
	 * This method initializes timeoutSlider	
	 * 	
	 * @return javax.swing.JSlider	
	 */
	private JSlider getTimeoutSlider() {
		JSlider timeoutSlider = new JSlider();
		
		timeoutSlider = new JSlider();
		timeoutSlider.setPaintLabels(true);
		
		return timeoutSlider;
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
			GridBagConstraints gridBagConstraints10 = new GridBagConstraints();
			gridBagConstraints10.gridx = 1;
			gridBagConstraints10.insets = new Insets(0, 5, 5, 0);
			gridBagConstraints10.anchor = GridBagConstraints.SOUTHEAST;
			gridBagConstraints10.weightx = 0.0;
			gridBagConstraints10.gridy = 1;
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
			panel.add(getApplyButton(), gridBagConstraints8);
			panel.add(getSplitPane(), gridBagConstraints9);
			panel.add(getOkButton(), gridBagConstraints10);
			panel.add(getCancelButton(), gridBagConstraints11);
		}
		return panel;
	}

	/**
	 * This method initializes applyButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getApplyButton() {
		if (applyButton == null) {
			applyButton = new JButton();
			applyButton.setText("Apply");
		}
		return applyButton;
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
		}
		return okButton;
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
		}
		return cancelButton;
	}

	/**
	 * This method initializes propertyPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getPropertyPanel() {
		if (propertyPanel == null) {
			GridBagConstraints gridBagConstraints13 = new GridBagConstraints();
			gridBagConstraints13.fill = GridBagConstraints.BOTH;
			gridBagConstraints13.gridy = 0;
			gridBagConstraints13.weightx = 0.7;
			gridBagConstraints13.anchor = GridBagConstraints.NORTHEAST;
			gridBagConstraints13.weighty = 0.0;
			gridBagConstraints13.gridx = 1;
			GridBagConstraints gridBagConstraints12 = new GridBagConstraints();
			gridBagConstraints12.gridx = 0;
			gridBagConstraints12.anchor = GridBagConstraints.WEST;
			gridBagConstraints12.weightx = 0.3;
			gridBagConstraints12.weighty = 1.0;
			gridBagConstraints12.gridy = 0;
			propertyLabel = new JLabel();
			propertyLabel.setText("Property Name");
			propertyPanel = new JPanel();
			propertyPanel.setLayout(new GridBagLayout());
			propertyPanel.setSize(new Dimension(289, 23));
			propertyPanel.add(propertyLabel, gridBagConstraints12);
			propertyPanel.add(getValueField(), gridBagConstraints13);
		}
		return propertyPanel;
	}

	/**
	 * This method initializes valueField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getValueField() {
		if (valueField == null) {
			valueField = new JTextField();
		}
		return valueField;
	}

	/**
	 * This method initializes propertyPanel2	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getPropertyPanel2() {
		if (propertyPanel2 == null) {
			GridBagConstraints gridBagConstraints14 = new GridBagConstraints();
			gridBagConstraints14.fill = GridBagConstraints.BOTH;
			gridBagConstraints14.gridy = 1;
			gridBagConstraints14.weightx = 1.0;
			gridBagConstraints14.weighty = 1.0;
			gridBagConstraints14.gridwidth = 2;
			gridBagConstraints14.insets = new Insets(3, 0, 0, 0);
			gridBagConstraints14.gridx = 0;
			GridBagConstraints gridBagConstraints131 = new GridBagConstraints();
			gridBagConstraints131.anchor = GridBagConstraints.NORTHEAST;
			gridBagConstraints131.gridx = 1;
			gridBagConstraints131.gridy = 0;
			gridBagConstraints131.weightx = 0.7;
			gridBagConstraints131.weighty = 0.0;
			gridBagConstraints131.fill = GridBagConstraints.BOTH;
			GridBagConstraints gridBagConstraints121 = new GridBagConstraints();
			gridBagConstraints121.anchor = GridBagConstraints.WEST;
			gridBagConstraints121.gridy = 0;
			gridBagConstraints121.weightx = 0.3;
			gridBagConstraints121.weighty = 1.0;
			gridBagConstraints121.gridx = 0;
			propertyLabel2 = new JLabel();
			propertyLabel2.setText("Property Name");
			propertyPanel2 = new JPanel();
			propertyPanel2.setLayout(new GridBagLayout());
			propertyPanel2.setSize(new Dimension(239, 37));
			propertyPanel2.add(propertyLabel2, gridBagConstraints121);
			propertyPanel2.add(getValueField2(), gridBagConstraints131);
			propertyPanel2.add(getPropertyExplanation(), gridBagConstraints14);
		}
		return propertyPanel2;
	}

	/**
	 * This method initializes valueField2	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getValueField2() {
		if (valueField2 == null) {
			valueField2 = new JTextField();
		}
		return valueField2;
	}

	/**
	 * This method initializes propertyExplanation	
	 * 	
	 * @return javax.swing.JTextArea	
	 */
	private JTextArea getPropertyExplanation() {
		if (propertyExplanation == null) {
			propertyExplanation = new JTextArea();
			propertyExplanation.setText("Explanation of this field....");
			propertyExplanation.setLineWrap(true);
		}
		return propertyExplanation;
	}
	
    private DefaultTableModel buildModel(String title, Object[] data) {
	DefaultTableModel model = new DefaultTableModel();

	model = new DefaultTableModel();
	model.addColumn(title);
	Object[] sep = { new TableSeperator() };

	for (int i = 0; i < data.length; i++) {
	    Object[] dat = { data[i] };
	    model.addRow(dat);
	    model.addRow(sep);

	}

	return model;
    }
	
	private Component getSMTResultsPanel()
	{
		return new JCheckBox("Show SMT-Results-Dialog after executing solvers.");
	}

	
	public static void main(String [] args){
		DPSDialog dialog = new DPSDialog();
		dialog.getJDialog().setVisible(true);
	}
	
	private void setModel(DefaultTableModel model){
		getOptionTable().setModel(model);
		
		
		for(int i=0; i < model.getRowCount(); i++){
		        if(model.getValueAt(i,0) instanceof TableComponent){
		            getOptionTable().setRowHeight(i, ((TableComponent)model.getValueAt(i,0)).getHeight());  
		        }
			
		}

	}
	
	private void init(){
	    	getOptionTree().setModel(getContentData());

		setModel(buildModel("General",getGeneralOptionsData()));


		getJScrollPane1().setViewportView(getOptionTable());
		
	}

}
