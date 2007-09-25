// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.FlowLayout;

import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTree;
import javax.swing.SwingUtilities;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreeCellRenderer;

import de.uka.ilkd.key.proof.RuleTreeModel;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.rule.Taclet;

public class RuleView extends JPanel implements TreeSelectionListener, java.io.Serializable {

    protected RuleTreeModel ruleViewModel    = null;
    protected JTree ruleTree;

    protected KeYMediator mediator = null;

    /** Listener for proof changes */
    protected SelectionListener selectionListener = new SelectionListener ();


    public RuleView () {
	layoutPane();
	ruleTree.setCellRenderer(new RuleRenderer());
	ruleTree.addTreeSelectionListener(this);
	setVisible ( true );
    }

    public void valueChanged(TreeSelectionEvent e){
    	if (ruleTree.getLastSelectedPathComponent() != null){
    		DefaultMutableTreeNode node = (DefaultMutableTreeNode)ruleTree.getLastSelectedPathComponent();
        	if(node.isLeaf()){
        		TacletView tv = TacletView.getInstance();
        		tv.showTacletView(node);
            } 
    	}    	
    }

    public void setMediator ( KeYMediator p_mediator ) {
	if ( mediator != null )
	    unregisterAtMediator ();
	
	mediator = p_mediator;
	registerAtMediator ();
	if ( mediator != null && mediator.getSelectedProof()!=null) {
	    setRuleTreeModel(new RuleTreeModel(mediator.getSelectedGoal()));
	}
    }


    protected void setRuleTreeModel(RuleTreeModel model) {

	ruleViewModel = model;

	if ( ruleViewModel != null ) {
	    ruleTree.setModel ( ruleViewModel );
	}
    }


    protected void registerAtMediator () {
	mediator.addKeYSelectionListener              ( selectionListener );
    }


    protected void unregisterAtMediator () {
	mediator.removeKeYSelectionListener           ( selectionListener );
    }


    protected void layoutPane() {
	setLayout(new BorderLayout());
	ruleTree = new JTree(new String[]{"No proof loaded"});
	add(ruleTree, BorderLayout.CENTER);
    }



    /**
     * Will be called when this dialog will be closed
     */
    protected void closeDlg(){
	//	mediator.freeModalAccess(this); 	
    }    


    private class SelectionListener implements KeYSelectionListener {

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	    ruleViewModel.setSelectedGoal(e.getSource().getSelectedGoal());
	}

	/** the selected proof has changed (e.g. a new proof has been
	 * loaded) */ 
	public void selectedProofChanged(KeYSelectionEvent e) {
            Runnable action = new Runnable () {
		public void run () {
		    if ( mediator != null && mediator.getSelectedProof()!=null)
			setRuleTreeModel(new RuleTreeModel
					 (mediator.getSelectedGoal()));
		}
	    };
        
	    if (SwingUtilities.isEventDispatchThread())  
                action.run();
            else  SwingUtilities.invokeLater(action);
	}
	
    }

    class RuleRenderer extends DefaultTreeCellRenderer 
	implements TreeCellRenderer,
		   java.io.Serializable {

	JPanel panel;
	JPanel statusPanel;
	JTextArea text;	

	public RuleRenderer() {
	    FlowLayout lay = new FlowLayout();
	    lay.setAlignment(FlowLayout.LEFT);	   	    
	    panel = new JPanel(lay);
	    statusPanel = new JPanel(lay);
	    text = new JTextArea();
	    panel.add(statusPanel);
	    panel.add(text);	    
	    text.setEditable(false);
	    text.setCaretPosition(0);
	}

	public Component getTreeCellRendererComponent(JTree tree,
						      Object value,
						      boolean sel,
						      boolean expanded,
						      boolean leaf,
						      int row,
						      boolean hasFocus) {
	    Component comp = super.getTreeCellRendererComponent
		(tree, value, sel, expanded, leaf, row, hasFocus);

            DefaultMutableTreeNode node = (DefaultMutableTreeNode)value;

	    if (node.getUserObject() instanceof OldOperationContract) {
		OldOperationContract mc = (OldOperationContract) node.getUserObject();
		comp = MethodContractList.makeMethodContractDisplay
		    (mc, panel, text, statusPanel,
		     sel ? super.backgroundSelectionColor : 
		     super.backgroundNonSelectionColor);
	    }
	    if (node.getUserObject() instanceof Taclet) {
		    
		Taclet t = (Taclet) node.getUserObject();
		String newValue = t.displayName();
		if (newValue.equals(node.getParent().toString())) {
		    newValue = t.name().toString(); // differentiated name
		}
		return super.getTreeCellRendererComponent(tree, 
		    newValue, sel, expanded, leaf, row, hasFocus);
	    }
	    return comp;


	}
    }


}
