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
import java.awt.Font;
import java.awt.event.*;
import java.io.File;
import java.util.LinkedList;
import java.util.List;

import javax.swing.*;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.notification.events.AbandonTaskEvent;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.*;
import de.uka.ilkd.key.util.Debug;

public class TaskTree extends JPanel {

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
        for (int i=0; i<proofs.length; i++) {
            proofs[i].addProofTreeListener(proofTreeListener);
        }
        delegateView.validate();	
        delegateView.scrollPathToVisible(new TreePath(bp.getPath()));	
        delegateView.setVisible(true);
        setVisible(true);
    }

    public void removeTask(TaskTreeNode tn) {

        int option = JOptionPane.showConfirmDialog(
                mediator.mainFrame(),"Are you sure?\n",
                "Abandon Proof", JOptionPane.YES_NO_OPTION);

        if (option == JOptionPane.YES_OPTION) {
	    removeTaskWithoutInteraction(tn);	    
        }
    }

    public void removeTaskWithoutInteraction(TaskTreeNode tn) {
        model.removeTask(tn);
	    mediator.notify(new AbandonTaskEvent());
	    for (int i=0; i<tn.allProofs().length; i++) {
		tn.allProofs()[i].removeProofTreeListener(proofTreeListener);
	    }
	    //go to some other node, take the last leaf.
	    TreePath path 
		= delegateView.getPathForRow(delegateView.getRowCount()-1);
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
	for (int i=0; i<paths.length; i++) {
	    if (paths[i].getLastPathComponent() instanceof BasicTask) {
		result.add((BasicTask) paths[i].getLastPathComponent());
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

    public void removeProof(Proof p) {
	// %% not implemented
    }

    
    /** inner class implementing the mouse listener that is responsible for 
     * this gui component
     */
    class TaskTreeMouseListener extends MouseAdapter {

	public void mouseClicked(MouseEvent e) {
	    if (e.getClickCount() == 1 
		&& e.getModifiers() != 
                   (MouseEvent.CTRL_MASK+MouseEvent.BUTTON1_MASK)) {
 		problemChosen();
 	    }
	}

	public void mousePressed(MouseEvent e) {
	    if (e.isPopupTrigger()) {
		TreePath selPath = delegateView.getPathForLocation
		    (e.getX(), e.getY());
		if (selPath!=null 
		    && selPath.getLastPathComponent() instanceof EnvNode) {
		    JPopupMenu popup = new ProofEnvPopupMenu
			(((EnvNode)selPath.getLastPathComponent()));
		    popup.show(e.getComponent(), e.getX(), e.getY());
		}
		if (selPath!=null 
		    && selPath.getLastPathComponent() instanceof BasicTask) {
		    JPopupMenu popup = new BasicTaskPopupMenu
			(((BasicTask)selPath.getLastPathComponent()));
		    popup.show(e.getComponent(), e.getX(), e.getY());
		}
		    
	    }
	}
        
        public void mouseReleased(MouseEvent e) {
            mousePressed(e);
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


    class ProofEnvPopupMenu extends JPopupMenu implements ActionListener {	
	
	private JMenuItem diffLast=new JMenuItem("Diff Last Env");
	
	private EnvNode invokedNode;

	public ProofEnvPopupMenu(EnvNode node) {
	    super("Choose Action");
	    invokedNode = node;
	    create();
	}

	private void create() {	    
	    this.add(diffLast);
	    diffLast.addActionListener(this);
	}

	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() == diffLast) {
		String s = invokedNode.getDiffToLast();
		JScrollPane scroll = new JScrollPane();
		JTextArea text = new JTextArea(s,20,40);
		text.setEditable(false);
		text.setCaretPosition(0);
		scroll.setViewportView(text);
		JFrame fr = new JFrame("Diff to Last Proof Environemnt");
		fr.getContentPane().setLayout(new BorderLayout());
		fr.getContentPane().add(scroll,BorderLayout.CENTER);
		JButton ok = new JButton("OK");
		ok.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
			    ((JFrame)((JButton)ae.getSource())
			     .getTopLevelAncestor()).dispose();
			}});
		fr.getContentPane().add(ok, BorderLayout.SOUTH);
		fr.setSize(600,900);
		fr.getContentPane().add(scroll);
		fr.setVisible(true);
	    } 
	}

    }


    class BasicTaskPopupMenu extends JPopupMenu implements ActionListener {	
	
        private JMenuItem mcList=new JMenuItem("Show Used Specifications");
        private JMenuItem loadProof=new JMenuItem("Load Proof from File");
        private JMenuItem removeTask=new JMenuItem("Abandon Task");
	
	private BasicTask invokedNode;

	public BasicTaskPopupMenu(BasicTask node) {
	    super("Choose Action");
	    invokedNode = node;
	    create();
	}

	private void create() {	    
	    this.add(mcList);
	    mcList.addActionListener(this);
	    this.add(loadProof);
	    loadProof.addActionListener(this);
            this.add(removeTask);
            removeTask.addActionListener(this);
	}


	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() == mcList) {
                new UsedSpecificationsDialog(
                            mediator.getServices(), 
                            invokedNode.getUsedSpecs());
	    } else if (e.getSource() == removeTask) {
	        removeTask(invokedNode);
            } else if (e.getSource() == loadProof) {
                Main mainFrame = Main.getInstance();
                KeYFileChooser localFileChooser = Main.getFileChooser(
                    "Choose file from which to load proof...");
                
	        boolean loaded = localFileChooser.showOpenDialog(mainFrame);
	        if (loaded) {
		    File file = localFileChooser.getSelectedFile(); 
		    final ProblemLoader pl = new ProblemLoader(file, mainFrame, 
                                        mediator.getProfile(), true);
                    pl.addTaskListener(mainFrame.getProverTaskListener());
                    pl.run();
	        }
            }
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



} // end of TaskTree


