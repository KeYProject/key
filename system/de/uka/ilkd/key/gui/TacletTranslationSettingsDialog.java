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
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.EventObject;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.JTree;
import javax.swing.UIManager;
import javax.swing.border.Border;
import javax.swing.event.CellEditorListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeCellEditor;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeNode;

import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;



public class TacletTranslationSettingsDialog extends JDialog implements TreeCellEditor{
    private final static TacletTranslationSettingsDialog instance 
    		= new TacletTranslationSettingsDialog();
    
    private JTree tree = new JTree();
    private JScrollPane scrollPane = new JScrollPane();

    private Color selectionBorderColor;

    private Color selectionForeground;

    private Color selectionBackground;

    private Color textForeground;

    private Color textBackground;
    
    private TacletTranslationSettingsDialog() {
	this.setTitle("Settings for taclet translation.");
	this.setSize(300, 400);
	this.setLayout(new BorderLayout());
	scrollPane = new JScrollPane(tree);
	tree.setModel(UsedTaclets.getTreeModel());
	this.getContentPane().add(scrollPane);
	tree.setCellRenderer(new NodeRenderer());
	tree.setCellEditor(this);
	tree.setEditable(true);

	

	
	
	
	selectionBorderColor = UIManager.getColor("Tree.selectionBorderColor");
	selectionForeground = UIManager.getColor("Tree.selectionForeground");
	selectionBackground = UIManager.getColor("Tree.selectionBackground");
	textForeground = UIManager.getColor("Tree.textForeground");
	textBackground = UIManager.getColor("Tree.textBackground");
    }
    
    //private SelectionPanel selectionPanel = new SelectionPanel();
    
    public static void showDialog(){
	instance.setVisible(true);
	
    }

    /* (non-Javadoc)
     * @see javax.swing.tree.TreeCellEditor#getTreeCellEditorComponent(javax.swing.JTree, java.lang.Object, boolean, boolean, boolean, int)
     */
    public Component getTreeCellEditorComponent(JTree tree, Object value,
            boolean selected, boolean expanded, boolean leaf, int row) {
	

    	DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
    	return SelectionPanel.getForInteraction(node,leaf,tree);
    	
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#addCellEditorListener(javax.swing.event.CellEditorListener)
     */
    public void addCellEditorListener(CellEditorListener arg0) {
	// TODO Auto-generated method stub
	
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#cancelCellEditing()
     */
    public void cancelCellEditing() {
	// TODO Auto-generated method stub
	
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#getCellEditorValue()
     */
    public Object getCellEditorValue() {
	// TODO Auto-generated method stub
	return null;
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#isCellEditable(java.util.EventObject)
     */
    public boolean isCellEditable(EventObject arg0) {
	// TODO Auto-generated method stub
	return true;
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#removeCellEditorListener(javax.swing.event.CellEditorListener)
     */
    public void removeCellEditorListener(CellEditorListener arg0) {
	// TODO Auto-generated method stub
	
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#shouldSelectCell(java.util.EventObject)
     */
    public boolean shouldSelectCell(EventObject arg0) {
	// TODO Auto-generated method stub
	return true;
    }

    /* (non-Javadoc)
     * @see javax.swing.CellEditor#stopCellEditing()
     */
    public boolean stopCellEditing() {
	// TODO Auto-generated method stub
	return false;
    }
}







class SelectionPanel extends JPanel{
    private final static SelectionPanel instanceForPainting = new SelectionPanel();
    private final static SelectionPanel instanceForClick = new SelectionPanel();
    
   
    private JCheckBox title = new JCheckBox();
    private JLabel chooseAll = new JLabel("<html><U>all</html>");
    private JLabel chooseNothing = new JLabel("<html><U>nothing</html>");
    private TreeItem currentItem = null;
    private DefaultMutableTreeNode currentNode = null;
    private JTree tree;
    
    private SelectionPanel(){
	
	this.setBackground(UIManager.getColor("Tree.textBackground"));
	title.setBackground(UIManager.getColor("Tree.textBackground"));
	title.setFont(UIManager.getFont("Tree.font"));
	chooseAll.setFont(UIManager.getFont("Tree.font"));
	chooseNothing.setFont(UIManager.getFont("Tree.font"));
	this.add(title);
	this.add(chooseAll);
	this.add(chooseNothing);
	
	title.addActionListener(new ActionListener(){

	    public void actionPerformed(ActionEvent event) {
	        currentItem.setChecked(title.isSelected());
	        parentSelection(currentNode,title.isSelected());
	        tree.repaint();
	    }	    
	});
	
	

	
	chooseAll.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e) {
	        title.setSelected(true);
	        select(currentNode,true);
	        
	        parentSelection(currentNode,title.isSelected());
	        tree.repaint();
            }
	});
	
	chooseNothing.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e) {
		title.setSelected(false);
		select(currentNode,false);
		
		parentSelection(currentNode,title.isSelected());
		tree.repaint();
		
            }
	});
	//title.setSize(title.getWidth(), 10);
    
    }
    
    private void parentSelection(DefaultMutableTreeNode node, boolean b){
	
	for(int i=0; i < node.getChildCount(); i++){
	    parentSelection((DefaultMutableTreeNode)node.getChildAt(i),b);
	    TreeItem item = (TreeItem)((DefaultMutableTreeNode)node.getChildAt(i)).getUserObject();
	    item.setParentSelected(b);
	}
    }
    
    private void select(DefaultMutableTreeNode node, boolean b){
	TreeItem item = (TreeItem)node.getUserObject();
	item.setChecked(b);
	for(int i=0; i < node.getChildCount(); i++){
	    select((DefaultMutableTreeNode)node.getChildAt(i),b);
	}
    }
    
    private void showSelection(boolean s){
	chooseAll.setVisible(s);
	chooseNothing.setVisible(s);
    
    }
    
    private void init(DefaultMutableTreeNode node, boolean isLeaf, JTree tree){
	currentNode = node;
	title.setText(currentNode.toString());
	currentItem = (TreeItem)node.getUserObject();
	title.setSelected(currentItem.isChecked());
	title.setEnabled(currentItem.isParentSelected());
	this.tree = tree;
	showSelection(!isLeaf);
	
    }
    
    static public SelectionPanel getForPainting(DefaultMutableTreeNode item, boolean isLeaf, JTree tree){
	instanceForPainting.init(item, isLeaf,tree);
	return instanceForPainting;}
    static public SelectionPanel getForInteraction(DefaultMutableTreeNode item, boolean isLeaf, JTree tree){
	instanceForClick.init(item, isLeaf,tree);
	return instanceForClick;}
}


class NodeRenderer implements TreeCellRenderer{

    /* (non-Javadoc)
     * @see javax.swing.tree.TreeCellRenderer#getTreeCellRendererComponent(javax.swing.JTree, java.lang.Object, boolean, boolean, boolean, int, boolean)
     */
    public Component getTreeCellRendererComponent(JTree tree, Object value,
            boolean selected, boolean expanded, boolean leaf, int row, boolean arg6) {
	DefaultMutableTreeNode node = (DefaultMutableTreeNode) value;
	return SelectionPanel.getForPainting(node,leaf,tree);
	
    }
    
}