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
import javax.swing.Box;
import javax.swing.DefaultCellEditor;
import javax.swing.JComboBox;
import javax.swing.JTextArea;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JSlider;
import javax.swing.JLabel;

import de.uka.ilkd.key.smt.SMTSolver;





public class DPSDialog {
    	public final static DPSDialog INSTANCE = new DPSDialog();
    	public final static Component    EMPTY_LINE = createSeperator();

    	TemporarySettings settings;
    	
    	DecisionProcedureSettings decSettings ;
    	TacletTranslationSettings tacletSettings;
    	
    	
    	public void showDialog(DecisionProcedureSettings set, TacletTranslationSettings tacletSet){
    	     settings = new TemporarySettings(set, tacletSet);
    	     
    	     decSettings = set;
    	     tacletSettings = tacletSet;
    	   init();
    	     getJDialog().setVisible(true);
    	    
    	    
    	}
    	

    private TableComponent[] getSolverData(TemporarySolverSettings tss){
	TableComponent data[] = {
		new TableProperty("Name:",tss.solver.name(),tss,false),
		new TableProperty("Installed:",tss.solver.isInstalled(false),tss,false),
		new TableProperty("Command:",tss.command,tss){
		    public void eventChange() {
			((TemporarySolverSettings)getUserObject()).command=getValue();
                    }    
		    protected boolean prepareProperty(){
			setValue(((TemporarySolverSettings)getUserObject()).command);
						
			return true;
		    }
		},
		
		new TableCheckBox(tss) {
		    
		    public boolean prepare() {
			setTitle("Use this prover for the rule 'multiple provers'.");
			setSelected(((TemporarySolverSettings)getUserObject()).useForMulitpleProvers);
			return true;
		    }
		    
		    @Override
		    public void eventChange() {
			((TemporarySolverSettings)getUserObject()).useForMulitpleProvers = isSelected();	
		    }
		}
		
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
	new TableComboBox(){

	    public void eventChange() {
		settings.progressDialogMode =(String) getSelectedItem();	        
            }

	    public boolean prepare() {
		
		setItems(DecisionProcedureSettings.PROGRESS_MODE_USER,
			 DecisionProcedureSettings.PROGRESS_MODE_CLOSE,
			 DecisionProcedureSettings.PROGRESS_MODE_CLOSE_FIRST,
			 DecisionProcedureSettings.PROGRESS_MODE_NO_DIALOG);
		setSelectedItem(settings.progressDialogMode);
	        return true;
            }
	    
	}
	
	,
	
	new TableCheckBox() {
	    
	    public boolean prepare() {
		setTitle("Cache goals.");
		setSelected(settings.cacheGoals);
		return true;
	    }
	    
	    @Override
	    public void eventChange() {
		settings.cacheGoals = isSelected();
		
	    }
	}
	
	,

	new TableSaveToFile("Save translation to file:") {

	    public boolean prepareProperties() {
		setFolder(settings.folder);
		setActivated(settings.storeToFile);
		enable(settings.storeToFile);
		return true;
	    }

	    public void eventChange() {
		settings.folder = getFolder();
		settings.storeToFile = isActivated();
		enable(isActivated());
		
	    }
	}

	};

	return data;

    }
    
    
    private TableComponent[] getTacletOptionsData() {
	TableComponent data[] = {




	new TableSaveToFile("Save taclet translation to file:") {

	    public boolean prepareProperties() {
		setFolder(settings.tacletFolder);
		setActivated(settings.storeTacletsToFile);
		enable(settings.storeTacletsToFile);
		return true;
	    }

	    public void eventChange() {
		settings.tacletFolder = getFolder();
		settings.storeTacletsToFile = isActivated();
		enable(isActivated());
		
	    }
	},
	new TableProperty("Maximum number of different generic sorts:",settings.maxGenerics,settings) {
	    public void eventChange() {
		int value;
		try{
		    value = Integer.parseInt(getValue()); 
		} catch(NumberFormatException e){
		    value = settings.maxGenerics;
		}
		settings.maxGenerics = value;
	    }
	    protected boolean prepareProperty() {
		setValue(settings.maxGenerics);
		return true;
	    };

	}

	};

	return data;

    }
    
    
	
	class OptionItem{
	
	    private String title;
	    private Component component;
	    private DefaultTableModel model;
	    
	    public String toString(){
		return title;
	    }
	    public OptionItem(String title) {
	        super();
	        this.title = title;
            }
	    
	    public OptionItem(String title,Component component){
		this(title);
		this.component = component;
	    }
	    
	    public OptionItem(String title, DefaultTableModel model){
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
	    
	    
	    
	    public void eventClicked(){
		if(model != null){
		    setModel(model);
		    getJScrollPane1().setViewportView(getOptionTable()); 
		}else if(component != null){
		    getJScrollPane1().setViewportView(component);
		}
		   
	    }
	    
	}
	
    private DefaultTreeModel getContentData() {
	if (contentModel == null) {
	    DefaultMutableTreeNode root = new DefaultMutableTreeNode();
	    root.setUserObject("Options");
	    DefaultTableModel model = buildModel(
		    "General", getGeneralOptionsData());
	    DefaultMutableTreeNode generalOptions = new DefaultMutableTreeNode();
	    generalOptions.setUserObject(new OptionItem("General", model));

	    DefaultMutableTreeNode solverOptions = new DefaultMutableTreeNode();
	    solverOptions.setUserObject("Solvers");
	    for (TemporarySolverSettings tss : settings.solverSettings) {
		DefaultMutableTreeNode solver = new DefaultMutableTreeNode();
		solver.setUserObject(new OptionItem(tss.toString(), buildModel(
		        tss.toString(), getSolverData(tss))));
		solverOptions.add(solver);
	    }

	    DefaultMutableTreeNode tacletOptions = new DefaultMutableTreeNode();
	    tacletOptions.setUserObject("Taclets");
	   
	    DefaultMutableTreeNode tacletSettings = new DefaultMutableTreeNode();
	    tacletSettings.setUserObject(new OptionItem("Settings", buildModel(
		    "Taclets", getTacletOptionsData())));
	    
	    DefaultMutableTreeNode tacletSelection = new DefaultMutableTreeNode();
	    tacletSelection.setUserObject(new OptionItem("Selection",
		    TacletTranslationSettingsDialog.INSTANCE.getSelectionPanel()));
	    tacletOptions.add(tacletSelection);
	    tacletOptions.add(tacletSettings);
	    

	    root.add(generalOptions);
	    root.add(solverOptions);
	    root.add(tacletOptions);

	    contentModel = new DefaultTreeModel(root);
	    setModel(model);
	    
	}else{
	    init((DefaultMutableTreeNode)contentModel.getRoot());
	}
	return contentModel;
    }
    
    void init(DefaultMutableTreeNode node){
	for(int i=0; i < node.getChildCount(); i ++){
	   init((DefaultMutableTreeNode)node.getChildAt(i));
	}
	if(node.getUserObject() instanceof OptionItem){
	    ((OptionItem)node.getUserObject()).init();
	}
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
	private DefaultTreeModel  contentModel = null;
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
			
			int left = getOptionTree().getPreferredSize().width, 
			    right= 600,
			    height = getOptionTable().getPreferredScrollableViewportSize().height;
			
			jDialog.setSize(new Dimension(left+right,(int) (1.25*height)));
			jDialog.setTitle("Decision Procedure Settings");
			jDialog.setContentPane(getJContentPane());
			jDialog.setLocationByPlatform(true);
			getSplitPane().setDividerLocation((int)(1.5*getOptionTree().getPreferredSize().width));
			
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
			   // ((TableComponent) value).eventChange();
			    
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
			    //((TableComponent) value).eventChange();
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
			applyButton.addActionListener(new ActionListener() {
			    
			    public void actionPerformed(ActionEvent e) {
				applyChanges();
			    }
			});
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
			okButton.addActionListener(new ActionListener() {
			    
			    public void actionPerformed(ActionEvent e) {
				getJDialog().setVisible(false);
				applyChanges();
			    }
			});
		}
		return okButton;
	}
	
	private void  applyChanges(){
	    settings.apply(decSettings,tacletSettings);
	    decSettings.fireSettingsChanged();
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

		//setModel(buildModel("General",getGeneralOptionsData()));


		getJScrollPane1().setViewportView(getOptionTable());
		
	}

}
