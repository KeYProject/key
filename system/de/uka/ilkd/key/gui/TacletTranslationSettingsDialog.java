// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.Insets;
import java.awt.ScrollPane;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.io.File;
import java.util.EventObject;
import java.util.Properties;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTree;
import javax.swing.UIManager;
import javax.swing.GroupLayout.Alignment;
import javax.swing.border.Border;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.CellEditorListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellEditor;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellEditor;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;


public class TacletTranslationSettingsDialog{

        private final static TacletTranslationSettingsDialog instance = new TacletTranslationSettingsDialog();
        private DefaultTreeCellRenderer cellRenderer = null;
	private JDialog optionsDialog = null;  //  @jve:decl-index=0:visual-constraint="40,9"
	private JPanel contentPane = null;
	private JTabbedPane tabbedPane = null;
	private JPanel selectionPanel = null;
	private JPanel optionsPanel = null;
	private JPanel saveFilePanel = null;
	private JPanel saveToFilePanel = null;
	private JTextField saveToFileField = null;
	private JButton saveToFileButton = null;
	private JCheckBox saveToFileBox = null;
	private JPanel translationPanel = null;
	private JTextField maxGenericField = null;
	private JLabel maxGenericLabel = null;
	private JPanel panelSelctionOptions = null;
	private JButton okButton = null;
	private JTree selectionTree = null;
	private JPanel selectionInfo = null;
	private JScrollPane scrollPane = null;
	private JLabel      infoLabel = null;
	/**
	 * This method initializes optionsDialog	
	 * 	
	 * @return javax.swing.JDialog	
	 */
	private JDialog getOptionsDialog() {
		if (optionsDialog == null) {
			optionsDialog = new JDialog();
			optionsDialog.setSize(new Dimension(490, 500));
			optionsDialog.setContentPane(getContentPane());
			optionsDialog.setTitle("Settings for taclet translation");
			
		}
		return optionsDialog;
	}

	/**
	 * This method initializes contentPane	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getContentPane() {
		if (contentPane == null) {
			contentPane = new JPanel();
			contentPane.setLayout(new BorderLayout());
			contentPane.add(getPanelSelctionOptions(), BorderLayout.CENTER);
		}
		return contentPane;
	}

	/**
	 * This method initializes tabbedPane	
	 * 	
	 * @return javax.swing.JTabbedPane	
	 */
	private JTabbedPane getTabbedPane() {
		if (tabbedPane == null) {
			tabbedPane = new JTabbedPane();
			tabbedPane.setName("");
			tabbedPane.addTab("Selection", null, getSelectionPanel(), null);
			tabbedPane.addTab("Options", null, getOptionsPanel(), null);
		}
		return tabbedPane;
	}

	/**
	 * This method initializes selectionPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getSelectionPanel() {
		if (selectionPanel == null) {
			GridBagConstraints gridBagConstraints10 = new GridBagConstraints();
			gridBagConstraints10.gridx = 1;
			gridBagConstraints10.fill = GridBagConstraints.VERTICAL;
			gridBagConstraints10.weightx = 0.0;
			gridBagConstraints10.weighty = 0.0;
			gridBagConstraints10.ipadx = 100;
			gridBagConstraints10.anchor = GridBagConstraints.NORTHEAST;
			gridBagConstraints10.gridy = 0;
			GridBagConstraints gridBagConstraints9 = new GridBagConstraints();
			gridBagConstraints9.fill = GridBagConstraints.BOTH;
			gridBagConstraints9.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints9.gridy = 0;
			gridBagConstraints9.weightx = 1.0;
			gridBagConstraints9.weighty = 1.0;
			gridBagConstraints9.ipadx =100;
			gridBagConstraints9.gridx = 0;
			selectionPanel = new JPanel();
			selectionPanel.setLayout(new GridBagLayout());
			selectionPanel.add(getScrollPane(), gridBagConstraints9);
			selectionPanel.add(getSelectionInfo(), gridBagConstraints10);
		
		}
		return selectionPanel;
	}
	/**
	 * This method initializes scrollPane	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	
	private JScrollPane getScrollPane(){
	    if(scrollPane == null){
		scrollPane = new JScrollPane(getSelectionTree());
		//scrollPane.add(getSelectionTree());
	    }
	    return scrollPane;
	}
	

	/**
	 * This method initializes optionsPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getOptionsPanel() {
		if (optionsPanel == null) {
			GridBagConstraints gridBagConstraints5 = new GridBagConstraints();
			gridBagConstraints5.gridx = 0;
			gridBagConstraints5.fill = GridBagConstraints.HORIZONTAL;
			gridBagConstraints5.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints5.weighty = 0.0;
			gridBagConstraints5.gridheight = 1;
			gridBagConstraints5.gridy = 0;
			GridBagConstraints gridBagConstraints4 = new GridBagConstraints();
			gridBagConstraints4.gridx = 0;
			gridBagConstraints4.fill = GridBagConstraints.HORIZONTAL;
			gridBagConstraints4.anchor = GridBagConstraints.NORTHWEST;
			gridBagConstraints4.weightx = 1.0;
			gridBagConstraints4.weighty = 1.0;
			gridBagConstraints4.gridheight = 1;
			gridBagConstraints4.gridy = 1;
			optionsPanel = new JPanel();
			optionsPanel.setLayout(new GridBagLayout());
			optionsPanel.add(getSaveToFilePanel(), gridBagConstraints4);
			optionsPanel.add(getTranslationPanel(), gridBagConstraints5);
		}
		return optionsPanel;
	}



	/**
	 * This method initializes saveToFilePanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getSaveToFilePanel() {
		if (saveToFilePanel == null) {
			GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
			gridBagConstraints2.gridx = 0;
			gridBagConstraints2.anchor = GridBagConstraints.WEST;
			gridBagConstraints2.gridy = 1;
			GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
			gridBagConstraints1.gridx = 1;
			gridBagConstraints1.weighty = 1.0;
			gridBagConstraints1.gridheight = 1;
			gridBagConstraints1.anchor = GridBagConstraints.WEST;
			gridBagConstraints1.fill = GridBagConstraints.NONE;
			gridBagConstraints1.weightx = 1.0;
			gridBagConstraints1.ipadx = 0;
			gridBagConstraints1.gridwidth = 1;
			gridBagConstraints1.gridy = 0;
			GridBagConstraints gridBagConstraints = new GridBagConstraints();
			gridBagConstraints.fill = GridBagConstraints.VERTICAL;
			gridBagConstraints.gridy = 0;
			gridBagConstraints.weightx = 0.1;
			gridBagConstraints.anchor = GridBagConstraints.WEST;
			gridBagConstraints.ipadx = 200;
			gridBagConstraints.gridwidth = 1;
			gridBagConstraints.insets = new Insets(0, 0, 0, 0);
			gridBagConstraints.gridx = 0;
			saveToFilePanel = new JPanel();
			saveToFilePanel.setLayout(new GridBagLayout());
			saveToFilePanel.setBorder(BorderFactory.createTitledBorder(null, "Save to file:", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			saveToFilePanel.add(getSaveToFileField(), gridBagConstraints);
			saveToFilePanel.add(getSaveToFileButton(), gridBagConstraints1);
			saveToFilePanel.add(getSaveToFileBox(), gridBagConstraints2);
		}
		return saveToFilePanel;
	}

	/**
	 * This method initializes saveToFileField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getSaveToFileField() {
		if (saveToFileField == null) {
			saveToFileField = new JTextField();
		}
		return saveToFileField;
	}

	/**
	 * This method initializes saveToFileButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getSaveToFileButton() {
		if (saveToFileButton == null) {
			saveToFileButton = new JButton();
			saveToFileButton.setText("choose");
			saveToFileButton.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					 JFileChooser fc = new JFileChooser();
					 fc.setDialogTitle("Select a file.");
					 fc.setMultiSelectionEnabled(false);
					 int returnVal = fc.showOpenDialog(Main.getInstance());
					 File target = fc.getSelectedFile();
					 if (returnVal == JFileChooser.APPROVE_OPTION) {
					     getSaveToFileField().setText(target.getAbsolutePath()); 
					    }
					 getOptionsDialog().setVisible(true);
				    
				   
				}
			});
		}
		return saveToFileButton;
	}

	/**
	 * This method initializes saveToFileBox	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	private JCheckBox getSaveToFileBox() {
		if (saveToFileBox == null) {
			saveToFileBox = new JCheckBox();
			saveToFileBox.setText("Save translation to file.");
		}
		return saveToFileBox;
	}

	/**
	 * This method initializes translationPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getTranslationPanel() {
		if (translationPanel == null) {
			GridBagConstraints gridBagConstraints6 = new GridBagConstraints();
			gridBagConstraints6.gridx = 0;
			gridBagConstraints6.gridy = 0;
			maxGenericLabel = new JLabel();
			maxGenericLabel.setText("Maximum of different generic sorts within a taclet:");
			GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
			gridBagConstraints3.fill = GridBagConstraints.VERTICAL;
			gridBagConstraints3.gridy = 0;
			gridBagConstraints3.weightx = 1.0;
			gridBagConstraints3.ipadx = 20;
			gridBagConstraints3.anchor = GridBagConstraints.WEST;
			gridBagConstraints3.insets = new Insets(0, 10, 0, 0);
			gridBagConstraints3.gridx = 1;
			translationPanel = new JPanel();
			translationPanel.setLayout(new GridBagLayout());
			translationPanel.setBorder(BorderFactory.createTitledBorder(null, "Translation", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			translationPanel.add(getMaxGenericField(), gridBagConstraints3);
			translationPanel.add(maxGenericLabel, gridBagConstraints6);
		}
		return translationPanel;
	}

	/**
	 * This method initializes maxGenericField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getMaxGenericField() {
		if (maxGenericField == null) {
			maxGenericField = new JTextField();
			maxGenericField.setText("3");
		}
		return maxGenericField;
	}

	/**
	 * This method initializes panelSelctionOptions	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getPanelSelctionOptions() {
		if (panelSelctionOptions == null) {
			GridBagConstraints gridBagConstraints8 = new GridBagConstraints();
			gridBagConstraints8.fill = GridBagConstraints.BOTH;
			gridBagConstraints8.gridy = 0;
			gridBagConstraints8.weightx = 1.0;
			gridBagConstraints8.weighty = 1.0;
			gridBagConstraints8.insets = new Insets(0, 0, 5, 0);
			gridBagConstraints8.gridx = 0;
			GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
			gridBagConstraints7.gridx = 0;
			gridBagConstraints7.anchor = GridBagConstraints.SOUTH;
			gridBagConstraints7.ipadx = 0;
			gridBagConstraints7.weightx = 1.0;
			gridBagConstraints7.insets = new Insets(0, 0, 5, 0);
			gridBagConstraints7.gridy = 1;
			panelSelctionOptions = new JPanel();
			panelSelctionOptions.setLayout(new GridBagLayout());
			panelSelctionOptions.add(getOkButton(), gridBagConstraints7);
			panelSelctionOptions.add(getTabbedPane(), gridBagConstraints8);
		}
		return panelSelctionOptions;
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
			okButton.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					try{
					    save();
					}catch(NumberFormatException ex){
		JOptionPane.showMessageDialog(null, ex.toString(), "Incorrect input", JOptionPane.OK_OPTION);
					    return;
					}
				     getOptionsDialog().setVisible(false);
				     ProofSettings.DEFAULT_SETTINGS
				      	.getTacletTranslationSettings()
				      	.fireSettingsHaveChanged();
				    
				}
			});
		}
		return okButton;
	}
	
	/**
	 * This method initializes selectionTree	
	 * 	
	 * @return javax.swing.JTree	
	 */
	private JTree getSelectionTree() {
		if (selectionTree == null) {
		    
			selectionTree = new JTree();
			selectionTree.setModel(UsedTaclets.getTreeModel());
			selectionTree.setCellRenderer(getTreeCellRenderer());
			selectionTree.setCellEditor(getTreeCellEditor());
			selectionTree.setEditable(true);

		}
		return selectionTree;
	}

	/**
	 * This method initializes selectionInfo	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getSelectionInfo() {
		if (selectionInfo == null) {
		      GridBagConstraints gridBagConstraints = new GridBagConstraints();
		   
			gridBagConstraints.fill = GridBagConstraints.BOTH;
			gridBagConstraints.gridy = 0;
			gridBagConstraints.weightx = 1.0;
			gridBagConstraints.weighty = 1.0;
			gridBagConstraints.ipadx = 100;
			gridBagConstraints.gridx = 1;
			
			selectionInfo = new JPanel();
			
			
			selectionInfo.setLayout(new GridBagLayout());
			//selectionInfo.setLayout(new BorderLayout());
			selectionInfo.setBorder(BorderFactory.createEtchedBorder(EtchedBorder.RAISED));
			//selectionInfo.add(getInfoLabel(),BorderLayout.CENTER);
			//selectionInfo.add(getInfoLabel(),gridBagConstraints);
		}
		return selectionInfo;
	}
	
	private JLabel getInfoLabel(){
	       if(infoLabel == null){
		   infoLabel=new JLabel();
		   
		  // infoLabel.setLineWrap(true);
		  
		    infoLabel.setText("<html>Changes in this<br>tab take effect<br>immediately without<br>pressing the OK-button.</html>");
	       }
	       return infoLabel;
	}
	
	private TreeCellEditor getTreeCellEditor() {
	    return new DefaultTreeCellEditor(getSelectionTree(),getTreeCellRenderer()){
		    public Component getTreeCellEditorComponent(JTree tree, Object value,
			    boolean selected, boolean expanded, boolean leaf, int row) {

			DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
			return SelectionPanel.getForInteraction(node, leaf, tree);

		    }
		    public boolean isCellEditable(EventObject arg0) {
			return true;
		    }
	    };
	}
	
	private DefaultTreeCellRenderer getTreeCellRenderer(){
	    if(cellRenderer == null){
		cellRenderer = new DefaultTreeCellRenderer(){
		    public Component getTreeCellRendererComponent(JTree tree, Object value,
			    boolean selected, boolean expanded, boolean leaf, int row,
			    boolean arg6) {
			DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
			return SelectionPanel.getForPainting(node, leaf, tree);

		    }
	    };
	    }
	    return cellRenderer;
	}
	
	
	/**
	 * Saves all current settings to the settings object.
	 * @throws NumberFormatException is thrown when the input of maxGeneric is
	 * incorrect.
	 */
	private void save() throws NumberFormatException{
	    TacletTranslationSettings tts = 
		ProofSettings.DEFAULT_SETTINGS.getTacletTranslationSettings();

	    tts.setMaxGeneric(Integer.valueOf(getMaxGenericField().getText()));
	   
	    tts.setFilename(getSaveToFileField().getText());
	    tts.setSaveToFile(getSaveToFileBox().isSelected()); 
	    
	    
	}
	
	/**
	 * Loads the settings from the settings object. <br>
	 * REMARK: The dialog does not need to load the assignment of the 
	 * taclet selection.
	 */
	private void init(){
	    TacletTranslationSettings tts = 
		ProofSettings.DEFAULT_SETTINGS.getTacletTranslationSettings();
	    // use defaults
	    if(tts == null){
		tts = TacletTranslationSettings.getInstance();
	    }
	    getMaxGenericField().setText(Integer.toString(tts.getMaxGeneric()));
	    getSaveToFileBox().setSelected(tts.isSaveToFile());
	    getSaveToFileField().setText(tts.getFilename());
	}
	
	/**
	 * Shows the settings dialog for taclet translation. 
	 */
	public static void showDialog(){
	    instance.init();
	    instance.getOptionsDialog().setVisible(true);
	}




}



/**
 * The SelectionPanel represents the graphical presentation of a
 * TreeItem and handles the input of the user.
 */
class SelectionPanel extends JPanel {
    private final static SelectionPanel instanceForPainting = new SelectionPanel();
    private final static SelectionPanel instanceForClick = new SelectionPanel();

    private JRadioButton title = new JRadioButton();
    private JLabel chooseAll = new JLabel("<html><U>all</html>");
    private JLabel chooseNothing = new JLabel("<html><U>nothing</html>");
    private JLabel countTaclets = new JLabel();
    private TreeItem currentItem = null;
    private DefaultMutableTreeNode currentNode = null;
    private JTree tree;

    private SelectionPanel() {

	this.setBackground(UIManager.getColor("Tree.textBackground"));
	title.setBackground(UIManager.getColor("Tree.textBackground"));
	title.setFont(UIManager.getFont("Tree.font"));
	chooseAll.setFont(UIManager.getFont("Tree.font"));
	chooseNothing.setFont(UIManager.getFont("Tree.font"));
	this.add(title);
	this.add(chooseAll);
	this.add(chooseNothing);
	// this.add(countTaclets);

	title.addActionListener(new ActionListener() {

	    public void actionPerformed(ActionEvent event) {
		selected(title.isSelected());
	    }
	});

	chooseAll.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e) {
		title.setSelected(true);
		
		selectAllNothing(currentNode, true);
		selected(true);
		
	    }
	});

	chooseNothing.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e) {
		title.setSelected(false);
		
		selectAllNothing(currentNode, false);
		selected(false);
	    }
	});
	// title.setSize(title.getWidth(), 10);

    }

    private TreeItem treeItem(TreeNode node) {
	return (TreeItem) ((DefaultMutableTreeNode) node).getUserObject();
    }
    
    /**
     * call this method after the item was checked or unchecked.
     * @param b the new value of the selection.
     */
    private void selected(boolean b){

        //setSelectedToRoot(currentNode);    
        if(title.isSelected()){
	    setSelectedToRoot(currentNode);
	  
	    setColor(Color.BLACK);
	}
        currentItem.setChecked(title.isSelected());
        parentSelection(currentNode, title.isSelected());
	tree.expandPath(tree.getEditingPath());
	

	tree.repaint();
	
	
    }

    /**
     * Checks all items on the path from <code>node</node>
     * to the root of the tree. 
     * @param node
     */
    private void setSelectedToRoot(TreeNode node) {
	TreeItem item = treeItem(node);
	parentSelection(node,true);
	item.setParentSelected(true);
	TreeNode parent = node.getParent();

	if (parent != null) {
	    item = treeItem(parent);
	    item.setChecked(true);
	    setSelectedToRoot(parent);
	    
	}

    }
    
    
    private void parentSelection(TreeNode node, boolean b) {
	for (int i = 0; i < node.getChildCount(); i++) {
	    parentSelection((DefaultMutableTreeNode) node.getChildAt(i), b);
	    TreeItem item = (TreeItem) ((DefaultMutableTreeNode) node
		    .getChildAt(i)).getUserObject();
	    item.setParentSelected(b);
	}
    }
    
    

    private void selectAllNothing(DefaultMutableTreeNode node, boolean b) {
	TreeItem item = (TreeItem) node.getUserObject();
	item.setChecked(b);
	for (int i = 0; i < node.getChildCount(); i++) {
	    selectAllNothing((DefaultMutableTreeNode) node.getChildAt(i), b);
	}
    }

    private void showSelection(boolean s) {
	chooseAll.setVisible(s);
	chooseNothing.setVisible(s);

    }
    
    private void setColor(Color color){
	title.setForeground(color);
	chooseAll.setForeground(color);
	chooseNothing.setForeground(color);
    }

    private void init(DefaultMutableTreeNode node, boolean isLeaf, JTree tree) {
	currentNode = node;
	title.setText(currentNode.toString());
	currentItem = (TreeItem) node.getUserObject();
	title.setSelected(currentItem.isChecked());
	// title.setEnabled(currentItem.isParentSelected());
	if(currentItem.isParentSelected()){
	    setColor(Color.BLACK);
	}else{
	    setColor(Color.GRAY);
	}
	this.tree = tree;
	showSelection(!isLeaf);

    }

    static public SelectionPanel getForPainting(DefaultMutableTreeNode item,
	    boolean isLeaf, JTree tree) {
	instanceForPainting.init(item, isLeaf, tree);
	return instanceForPainting;
    }

    static public SelectionPanel getForInteraction(DefaultMutableTreeNode item,
	    boolean isLeaf, JTree tree) {
	instanceForClick.init(item, isLeaf, tree);
	return instanceForClick;
    }
}


