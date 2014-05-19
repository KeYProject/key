// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Font;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.LinkedList;
import java.util.List;

import javax.swing.ImageIcon;
import javax.swing.JPanel;
import javax.swing.JTree;
import javax.swing.UIManager;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.notification.events.AbandonTaskEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.mgt.BasicTask;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.util.Debug;

public class TaskTree extends JPanel {

    /**
     * 
     */
    private static final long serialVersionUID = -6084969108377936099L;

    private JTree delegateView;

    /** the KeYMediator */
    private KeYMediator mediator;
    
    /** listener for mouse events of this gui component */
    private MouseListener mouseListener = new TaskTreeMouseListener();

    /** listener to the prof tree events */
    private ProofTreeListener proofTreeListener 
	= new TaskTreeProofTreeListener();

    /** the list model to be used */
    private TaskTreeModel model = new TaskTreeModel();

    public TaskTree(KeYMediator mediator) {
	super();
	this.mediator = mediator;
	mediator.addKeYSelectionListener(new TaskTreeSelectionListener());
	delegateView=new JTree();
	delegateView.setModel(model);   
	delegateView.setCellRenderer(new TaskTreeIconCellRenderer());
	delegateView.addMouseListener(mouseListener);
	this.setLayout(new BorderLayout());
	this.add(delegateView,BorderLayout.CENTER);
 	delegateView.setShowsRootHandles(false);
 	delegateView.setRootVisible(false);
 	delegateView.putClientProperty("JTree.lineStyle", "Horizontal");
    }

    JTree jtree() {
	return delegateView;
    }

    public void addProof(de.uka.ilkd.key.proof.ProofAggregate plist) {
        TaskTreeNode bp = model.addProof(plist);
        Proof[] proofs = plist.getProofs();
        for (Proof proof : proofs) {
            proof.addProofTreeListener(proofTreeListener);
        }
        delegateView.validate();	
        delegateView.scrollPathToVisible(new TreePath(bp.getPath()));	
        delegateView.setVisible(true);
        setVisible(true);
    }

    public void removeTask(TaskTreeNode tn) {
        model.removeTask(tn);
	    mediator.notify(new AbandonTaskEvent());
	    for (int i=0; i<tn.allProofs().length; i++) {
		tn.allProofs()[i].removeProofTreeListener(proofTreeListener);
                tn.allProofs()[i].mgt().removeProofListener();
	    }
            MainWindow.getInstance().getProofView().
                removeProofs(tn.allProofs());
	    //go to some other node, take the last leaf.
	    TreePath path 
		= delegateView.getPathForRow(delegateView.getRowCount()-1);
	    if(mediator.getInteractiveProver()!=null){
	        mediator.getInteractiveProver().clear();
	    }
	    if (path!=null) {
		TaskTreeNode tn0 = (TaskTreeNode) path.getLastPathComponent();
		mediator.setProof(tn0.proof());
	    } else {
		mediator.setProof(null);
	    }
    }
    
    public void updateUI() {
	super.updateUI();
	Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_LIST_VIEW);
	if (myFont != null) {
	    setFont(myFont);
	} else {
	    Debug.out(Config.KEY_FONT_PROOF_LIST_VIEW + 
		      " not available, use standard font.");
	}
    }

    /** returns the first selected task which is instance of a task tree node
     */
    public TaskTreeNode getSelectedTask() {
	TreePath path = delegateView.getSelectionModel().getSelectionPath();
	if (path!=null && path.getLastPathComponent() instanceof TaskTreeNode) {
	    return (TaskTreeNode) path.getLastPathComponent();
	} else {
	    return null;
	}
    }

    /** returns all selected basic tasks */
    public BasicTask[] getAllSelectedBasicTasks() {
	TreePath[] paths 
	    = delegateView.getSelectionModel().getSelectionPaths();
	if (paths==null) return new BasicTask[0];
        final List<BasicTask> result = new LinkedList<BasicTask>();
        for (TreePath path : paths) {
            if (path.getLastPathComponent() instanceof BasicTask) {
                result.add((BasicTask)path.getLastPathComponent());
            }
        }
	return result.toArray(new BasicTask[result.size()]);
    }

    /** called when the user has clicked on a problem */
    private void problemChosen() {
	TaskTreeNode prob = getSelectedTask();
	if (prob != null && prob.proof()!=null && mediator != null) {
	    mediator.setProof(prob.proof());
	} 
    }

    /**
     * <p>
     * Checks if the given {@link Proof} is contained in the model.
     * </p>
     * <p>
     * This functionality is required for instance for the symbolic execution
     * debugger to check if a {@link Proof} is still available in KeY's
     * {@link MainWindow} or not, because if it was removed the auto mode is
     * no longer available.
     * </p>
     * @param proof The {@link Proof} to check.
     * @return {@code true} proof is available in model, {@code false} proof is not available in model.
     */
    public boolean containsProof(Proof proof) {
       boolean contains = false;
       int i = 0;
       while (!contains && i < model.getChildCount(model.getRoot())) {
          Object rootChild = model.getChild(model.getRoot(), i);
          if (rootChild instanceof EnvNode) {
             EnvNode envNode = (EnvNode)rootChild;
             int j = 0;
             while (!contains && j < envNode.getChildCount()) {
                Object envChild = envNode.getChildAt(j);
                if (envChild instanceof TaskTreeNode) {
                   TaskTreeNode taskChild = (TaskTreeNode)envChild;
                   contains = taskChild.proof() == proof;
                }
                j++;
             }
          }
          i++;
       }
       return contains;
    }
    
    /**
     * Removes the given proof from the model.
     * @param proof The proof to remove.
     */
    public void removeProof(Proof proof) {
       if (proof != null) {
          ProofEnvironment env = proof.env();
          // Search EnvNode which contains the environment of the given proof.
          EnvNode envNode = null;
          for (int i = 0; i < model.getChildCount(model.getRoot()); i++) {
             Object child = model.getChild(model.getRoot(), i);
             if (child instanceof EnvNode) {
                EnvNode envChild = (EnvNode)child;
                if (env != null ? env.equals(envChild.getProofEnv()) : envChild.getProofEnv() == null) {
                   envNode = envChild;
                }
             }
          }
          // Remove proof from found environment node.
          if (envNode != null) {
             for (int i = 0; i < envNode.getChildCount(); i++) {
                Object child = envNode.getChildAt(i);
                if (child instanceof TaskTreeNode) {
                   TaskTreeNode taskChild = (TaskTreeNode)child;
                   if (taskChild.proof() == proof) {
                      removeTask(taskChild);
                   }
                }
             }
          }
       }
    }

    
    /** inner class implementing the mouse listener that is responsible for 
     * this gui component
     */
    class TaskTreeMouseListener extends MouseAdapter {

    	public void mouseClicked(MouseEvent e) {
    		problemChosen();
    	}
    }


    /** a prooftree listener, so that it is known when the proof has closed 
     */
    class TaskTreeProofTreeListener extends ProofTreeAdapter {
	
	/** invoked if all goals of the proof are closed
	 */
	public void proofClosed(ProofTreeEvent e) {	
	    delegateView.repaint();
	}
	
	/** invoked if the list of goals changed (goals were added,
	 * removed etc.
	 */
	public void proofGoalRemoved(ProofTreeEvent e) {
	}
	
	/** invoked if the current goal of the proof changed */
	public void proofGoalsAdded(ProofTreeEvent e) {
	}
	
	/** invoked if the current goal of the proof changed */
	public void proofGoalsChanged(ProofTreeEvent e) {
	}
    } // end of prooftreelistener


    static class TaskTreeIconCellRenderer extends DefaultTreeCellRenderer
				             implements java.io.Serializable { 
	
	/**
         * 
         */
        private static final long serialVersionUID = 4580251672266092290L;
    static final ImageIcon keyIcon=IconFactory.keyHole(20,20);
	static final ImageIcon keyClosedIcon=IconFactory.keyHoleClosed(20,20);
	static final ImageIcon keyAlmostClosedIcon
	    =IconFactory.keyHoleAlmostClosed(20,20);


	public TaskTreeIconCellRenderer() {
	    setToolTipText("Task");	 
	}
	
	public Component getTreeCellRendererComponent
	    (JTree list,
	     Object value, 
	     boolean selected,
	     boolean expanded,
	     boolean leaf,
	     int row,
	     boolean hasFocus) 
	{
	    Object newValue;
 	    if (value instanceof TaskTreeNode) {
		newValue=((TaskTreeNode)value).shortDescr();
	    } else {
 		newValue=value;
	    }
	    DefaultTreeCellRenderer sup=(DefaultTreeCellRenderer)
		super.getTreeCellRendererComponent(list, newValue, 
						   selected, expanded,
						   leaf, row,
						   hasFocus);
	    sup.setIcon(null);		
	    if (value instanceof TaskTreeNode) {
		ProofStatus ps = ((TaskTreeNode)value).getStatus();
		if (ps!=null) {
		    if (ps.getProofClosed()) sup.setIcon(keyClosedIcon);
		    if (ps.getProofClosedButLemmasLeft()) 
			sup.setIcon(keyAlmostClosedIcon);
		    if (ps.getProofOpen()) sup.setIcon(keyIcon);
		}
		
	    } 
	    return sup;
	}
    } 


    class TaskTreeSelectionListener implements KeYSelectionListener {
	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	    // empty
	}

	/** the selected proof has changed (e.g. a new proof has been
	 * loaded) 
	 */ 
	public void selectedProofChanged(KeYSelectionEvent e) {
	    if (e.getSource().getSelectedProof()==null) {
		return;
	    }
	    TaskTreeNode ttn 
		= model.getTaskForProof(e.getSource().getSelectedProof());
	    jtree().setSelectionPath(new TreePath(ttn.getPath()));
	    validate();
	}
	
    }
    
    /**
     * Returns the shown {@link TaskTreeModel}.
     * @return The shown {@link TaskTreeModel}.
     */
    public TaskTreeModel getModel() {
       return model;
    }
} // end of TaskTree