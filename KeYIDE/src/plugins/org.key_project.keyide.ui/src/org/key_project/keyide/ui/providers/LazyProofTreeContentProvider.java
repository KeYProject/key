/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.keyide.ui.providers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.testing.ContributionInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * A class to provide the proofTree transformed to the KeY-Internal
 * representation.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class LazyProofTreeContentProvider implements ILazyTreeContentProvider {
   /**
    * The {@link ProofControl} of the {@link Proof} which offers the proof tree to show.
    */
   private ProofControl pc;
   
	/**
	 * A mapping from {@link Node}s to {@link BranchFolder}s.
	 */
	private final Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();

	/**
	 * The ProofTreeListener
	 */
	private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
		/**
		 * {@inheritDoc}
		 */
		@Override
		public void proofPruned(ProofTreeEvent e) {
			handleProofPruned(e);
		}

		/**
		 * {@inheritDoc}
		 */
		@Override
		public void proofExpanded(ProofTreeEvent e) {
			handleProofExpanded(e);
		}
	};
	
	/**
	 * Listens for start and stop of the auto mode.
	 */
	private final AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStarted(ProofEvent e) {
         handleAutoModeStarted(e);
      }

      @Override
      public void autoModeStopped(ProofEvent e) {
         handleAutoModeStopped(e);
      }
	};

	/**
	 * The {@link TreeViewer} in which this {@link ILazyTreeContentProvider} is
	 * used.
	 */
	private TreeViewer viewer;

	/**
	 * The {@link Proof} as input of {@link #viewer}.
	 */
	private Proof proof;
	
	/**
	 * The boolean flag which indicates hiding or showing of intermediate proofsteps.
	 */
	private boolean hideState;
	
	/**
	 * The boolean flag for the show symbolic execution tree only outline filter.
	 */
	private boolean symbolicState;
	
	/**
	 * The boolean flag for the show subtree of node filter.
	 */
	private boolean showSubtree;
	
	/**
	 * The root of the show subtree of node filtered proof tree.
	 */
	private Node newRoot;
	
	/**
	 * The {@link Goal}s on which the auto mode operates.
	 */
	private ImmutableList<Node> goalsOfAutomode;
	
	/**
	 * The Constructor
	 */
	public LazyProofTreeContentProvider(ProofControl pc) {
	   this.pc = pc;
		this.hideState = false;
		this.symbolicState = false;
		this.showSubtree = false;
		if (pc != null) {
		   pc.addAutoModeListener(autoModeListener);
		}
	}

   /**
	 * {@inheritDoc}
	 */
	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		Assert.isTrue(viewer instanceof TreeViewer);
		this.viewer = (TreeViewer) viewer;
		if (proof != null && !proof.isDisposed()) {
			proof.removeProofTreeListener(proofTreeListener);
		}
		if (newInput instanceof Proof) {
			this.proof = (Proof) newInput;
		}
		else if (newInput instanceof Node) {
		   this.proof = ((Node) newInput).proof();
		}
		else {
			this.proof = null;
		}
      if (proof != null && !proof.isDisposed()) {
         proof.addProofTreeListener(proofTreeListener);
      }
	}
	
	public void setProofControl(ProofControl pc) {
	   if (this.pc != null) {
	      this.pc.removeAutoModeListener(autoModeListener);
	   }
	   this.pc = pc;
      if (this.pc != null) {
         this.pc.addAutoModeListener(autoModeListener);
      }
	}

	/**
	 * When the auto mode is started.
	 * @param e The event.
	 */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.removeProofTreeListener(proofTreeListener);
         ImmutableList<Goal> goals = proof.openEnabledGoals();
         goalsOfAutomode = ImmutableSLList.<Node>nil();
         for (Goal goal : goals) {
            goalsOfAutomode = goalsOfAutomode.prepend(goal.node());
         }
      }
   }
   
   /**
    * When the auto mode stopps.
    * @param e The event.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.addProofTreeListener(proofTreeListener);
         if (!viewer.getControl().isDisposed()) {
            viewer.getControl().getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  if (!viewer.getControl().isDisposed()) {
                     updateOriginalGoalNodesAfterAutoModeStopped();
                  }
               }
            });
         }
      }
   }
   
   /**
    * Ensures that the viewer shows the full proof tree after the auto mode has stopped.
    */
   protected void updateOriginalGoalNodesAfterAutoModeStopped() {
      if (goalsOfAutomode != null) {
         for (Node node : goalsOfAutomode) {
            Object parent = getParent(node);
            // Update child count of parent
            int childCount = doUpdateChildCount(parent, -1);
            // Ensure that all children below the parents are known. This is required under Eclipse 4.5 and 4.6.
            // Other ancestors (children of children) are later loaded lazily by the viewer. 
            for (int i = 0; i < childCount; i++) {
               updateElement(parent, i);
            }
         }
         goalsOfAutomode = null;
      }
   }

	/**
	 * Ensures that all top level elements are shown which is required in
	 * Eclipse 4.4... :-(
	 */
	public void injectTopLevelElements() {
		int childCount = doUpdateChildCount(proof, -1);
		for (int i = 0; i < childCount; i++) {
			updateElement(proof, i);
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public Object getParent(Object element) {
		if (element instanceof BranchFolder) {
			BranchFolder branchFolder = (BranchFolder) element;
			element = branchFolder.getChild().parent();
		}
		if (element instanceof Node) {
			// Iterate back in parent hierarchy until a branching node is found
			Node nonBranchingNode = (Node) element;

			if (!showSubtree) {
				while (nonBranchingNode.parent() != null && nonBranchingNode.parent().childrenCount() == 1) {
					nonBranchingNode = nonBranchingNode.parent();
   			}
			} else {
				while (nonBranchingNode != newRoot && nonBranchingNode.parent() != null && nonBranchingNode.parent().childrenCount() == 1) {
					nonBranchingNode = nonBranchingNode.parent();
				}
				if (nonBranchingNode == newRoot || proof == null || proof.isDisposed() || nonBranchingNode == proof.root()) {
					return proof;
				}
			}
			// Check if the root of the proof was found
			if (nonBranchingNode.parent() == null) {
				return proof;
			} else {
				// Get branch folder
				BranchFolder bf = branchFolders.get(nonBranchingNode);
				// Create branch folder if not available.
				if (bf == null) {
					bf = new BranchFolder(nonBranchingNode);
					branchFolders.put(nonBranchingNode, bf);
				}
				return bf;
			}
		} else {
			return null;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void updateChildCount(Object element, int currentChildCount) {
		doUpdateChildCount(element, currentChildCount);
	}

   /**
	 * Performs the steps of {@link #updateChildCount(Object, int)}.
	 * 
	 * @param element
	 *            The element to update its child count.
	 * @param currentChildCount
	 *            The current number of children.
	 * @return The new updated number of children.
	 */
	protected int doUpdateChildCount(Object element, int currentChildCount) {
      if (element instanceof Node) {
         viewer.setChildCount(element, 0); // A node has never children, only BranchFolders have children.
         return 0;
      }
      else if (element instanceof BranchFolder) {
			BranchFolder branchFolder = (BranchFolder) element;
			Node branchNode = branchFolder.getChild();
			int childCount = getBranchFolderChildCount(branchNode);
			int folderCount = getFolderCountInBranch(branchFolder);
			viewer.setChildCount(element, childCount + folderCount);
			return childCount + folderCount;
		}
      else if (element instanceof Proof) {
         Proof currentProof = (Proof) element;
         Node root = currentProof.root();
         if (showSubtree) {
            root = newRoot;
         }
         int childCount = getBranchFolderChildCount(root);
         int folderCount = getFolderCountInBranch(currentProof);
         viewer.setChildCount(element, childCount + folderCount);
         return childCount + folderCount;
      }
      else {
			return 0;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void updateElement(Object parent, int index) {
		Object element = getElementByIndex(parent, index);
		viewer.replace(parent, index, element);
		updateChildCount(element, -1);
	}

	/**
	 * When a {@link Node} was pruned.
	 * 
	 * @param e
	 *            The event.
	 */
	protected void handleProofPruned(final ProofTreeEvent e) {
		Display display = viewer.getControl().getDisplay();
		if (!display.isDisposed()) {
			display.asyncExec(new Runnable() {
				@Override
				public void run() {
					if (!viewer.getControl().isDisposed()) {
						doHandleProofPruned(e.getNode());
					}
				}
			});
		}
	}

	/**
	 * Performs the steps required to handle a pruned {@link Node}.
	 * 
	 * @param node
	 *            The expanded {@link Node}.
	 */
	protected void doHandleProofPruned(Node node) {
		doUpdateChildCount(getParent(node), -1);
	}

	/**
	 * When a {@link Node} was expanded.
	 * 
	 * @param e
	 *            The event.
	 */
	protected void handleProofExpanded(final ProofTreeEvent e) {
		viewer.getControl().getDisplay().asyncExec(new Runnable() {
			@Override
			public void run() {
				if (!viewer.getControl().isDisposed()) {
					doHandleProofExpanded(e.getNode());
				}
			}
		});
	}

	/**
	 * Performs the steps required to handle an expanded {@link Node}.
	 * 
	 * @param node
	 *            The expanded {@link Node}.
	 */
	protected void doHandleProofExpanded(Node node) {
		Object parent = getParent(node);
		// Update child count of parent
		int childCount = doUpdateChildCount(parent, -1);
		// Make new nodes visible to tree. This is required under Eclipse 4.5 and 4.6.
		for (int i = 0; i < node.childrenCount(); i++) {
		   updateElement(parent, childCount - 1 - i);
		}
	}

	/**
	 * Returns the number of {@link Node}s in the branch of the given
	 * {@link Node}. {@link BranchFolder}s in this branch will not be counted.
	 * 
	 * @param node
	 *            - any {@link Node} out of the branch.
	 * @return the number of {@link Node}s in the branch.
	 */
	protected int getBranchFolderChildCount(Node node) {
		Node branchNode = getBranchNode(node);
		int count;
		if (!hideState && symbolicState) {
			Node startNode = branchNode;
			count = 0; // counter for execution nodes
			int nodeCount = 1; // counter for all nodes
			boolean termination = false; // indicates if a termination node was found
			
			if (isExecutionNode(branchNode)) {
				count = 1;
				if (SymbolicExecutionUtil.isTerminationNode(branchNode, branchNode.getAppliedRuleApp())) {
					termination = true;
				}
			}
			if (showSubtree && branchNode == newRoot) {
			   count = 1;
			}
			
			while (branchNode.childrenCount() == 1) {
				branchNode = branchNode.child(0);
				if (isExecutionNode(branchNode)) {
					count++;
					if (SymbolicExecutionUtil.isTerminationNode(branchNode, branchNode.getAppliedRuleApp())) {
						termination = true;
					}
				} else if (termination) {
					count++;
				}
				nodeCount++;
			}
			
			// if no execution node was found
			if (count == 0) {
				while (startNode.parent() != null && !showSubtree || branchNode != newRoot && showSubtree) {
					startNode = startNode.parent();
					if (isExecutionNode(startNode)) {
						if (SymbolicExecutionUtil.isTerminationNode(startNode, startNode.getAppliedRuleApp())) {
							count = nodeCount;
							break;
						} else if (isExecutionNode(startNode)) {
							break;
						}
					}
				}
			}
		}
		else if (hideState) {
         // Skip over hidden nodes
         while (branchNode.childrenCount() == 1) {
            branchNode = branchNode.child(0);
         }
         if (branchNode.leaf()) {
            count = 1; // The open goal
         }
         else {
            count = 0; // Child branch folders are not counted!
         }
		}
		else {
		   // Count the number of children on the same branch.
			count = 1;
			while (branchNode.childrenCount() == 1) {
				branchNode = branchNode.child(0);
				count += 1;
			}
		}
		return count;
	}

	/**
	 * Returns the branch{@link Node} respectively the first child {@link Node}
	 * in its branch.
	 * 
	 * @param node
	 *            - any {@link Node} out of the branch.
	 * @return the branch{@link Node} respectively the first child {@link Node}
	 *         in its branch.
	 */
	protected Node getBranchNode(Node node) {
		
	   if (!showSubtree) {
   		while (true) {
   			if (node.equals(node.proof().root()) || node.parent().childrenCount() > 1) {
   				return node;
   			} else {
   				node = node.parent();
   			}
   		}
	   } else {
	      while (true) {
            if (node.equals(newRoot)
                  || node.parent().childrenCount() > 1) {
               return node;
            } else {
               node = node.parent();
            }
         }
	   }
	}

	/**
	 * Returns the element for the given parent and index. This method can
	 * handle the inputs iff instanceof {@link Proof} or {@link BranchFolder}.
	 * 
	 * @param parent
	 *            - the parent object respectively the branches root.
	 * @param index
	 *            - the index of the element in its branch
	 * @return the element for the given parent and index.
	 */
	protected Object getElementByIndex(Object parent, int index) {
		Node node = null;
		int childCount = 0;
		if (parent instanceof ContributionInfo) {
			node = proof.root();
			if (showSubtree) {
			   node = newRoot;
			}
			childCount = getBranchFolderChildCount(node);
		}
		else if (parent instanceof Proof) {
			Proof currentProof = (Proof) parent;
			node = currentProof.root();
			if (showSubtree) {
			   node = newRoot;
			}
			childCount = getBranchFolderChildCount(node);
		}
		else if (parent instanceof BranchFolder) {
			BranchFolder branchFolder = (BranchFolder) parent;
			node = branchFolder.getChild();
         childCount = getBranchFolderChildCount(node);
		}
		// element is a Node
		if (index < childCount) {
			if (hideState) {
				while (node.childrenCount() == 1) {
					node = node.child(0);
				}
			}
			else if (symbolicState) {
				Node startNode = node;
				int count = -1;
				boolean termination = false; // indicates if a termination node was found
				
				if (isExecutionNode(node)) {
					count = 0;
					if (SymbolicExecutionUtil.isTerminationNode(node, node.getAppliedRuleApp())) {
						termination = true;
					}
				}
				
				while (node.childrenCount() == 1 && count < index) {
					node = node.child(0);
					if (isExecutionNode(node)) {
						count++;
						if (SymbolicExecutionUtil.isTerminationNode(node, node.getAppliedRuleApp())) {
							termination = true;
						}
					} else if (termination) {
						count++;
					}
				}
				
				// if not was not found in subtree
				Node parentNode = startNode;
				if (count < index) {
					while (parentNode.parent() != null && !showSubtree || parentNode != newRoot && showSubtree) {
						parentNode = parentNode.parent(); 
						if (SymbolicExecutionUtil.isTerminationNode(parentNode, parentNode.getAppliedRuleApp())) {
							node = startNode;
							for (int i = 0; i < index; i++) {
								node = node.child(0);
							}
							break;
						} else if (isExecutionNode(parentNode)) {
							return null;
						}
					}
				}
			}
			else {
				// gets the right node when no filter is active
				for (int i = 0; i < index; i++) {
					node = node.child(0);
				}
			}
			return node;
		}
		// element is a BranchFolder (as long as hide intermediate state is not enabled)
		else {
         int folderIndex = index - childCount;
         while (node.childrenCount() == 1) {
            node = node.child(0);
         }
		   if (hideState && node.leaf()) {
		      // element is the goal instead of a branch folder
		      return node;
		   }
		   else {
	         // element is a BranchFolder
	         BranchFolder branchFolder = new BranchFolder(node.child(folderIndex));
	         branchFolders.put(node.child(folderIndex), branchFolder);
	         return branchFolder;
		   }
		}
	}
	
	/**
	 * Returns the index of the given element at its given parent.
	 * 
	 * @param parent
	 *            The parent to search in.
	 * @param element
	 *            The element to compute its child index.
	 * @return The child index of the element or {@code -1} if it is not a child
	 *         of the parent.
	 */
	public int getIndexOf(Object parent, Object element) {
		// Make sure that parameters are valid
		Assert.isTrue(element instanceof BranchFolder || element instanceof Node, "Unsupported element \"" + ObjectUtil.getClass(element) + "\".");
		Assert.isTrue(parent instanceof Proof || parent instanceof BranchFolder || parent instanceof Node, "Unsupported parent \"" + ObjectUtil.getClass(parent) + "\".");
		// Find first shown child node of the given parent
		Node current = null;
		if (parent instanceof Proof) {
			current = ((Proof) parent).root();
			if (showSubtree) {
			   current = newRoot;
			}
		}
		else if (parent instanceof BranchFolder) {
			current = ((BranchFolder) parent).getChild();
		}
		
		boolean termination = false; // indicates if a termination node was found
		int index = 0;
		if (hideState) {
			// returns -1 for every intermediate proof step when the filter is active
			if (element instanceof Node) {
				Node node = (Node) element;
				if (!node.leaf()) {
					return -1;
				} else {
					return 0;
				}
			}
		} 
		else if (symbolicState) {
			if (element instanceof Node) {
				Node node = (Node) element;
				if (!isExecutionNode(node)) {
					Node parentNode = node;
					while (parentNode.parent() != null && !showSubtree || parentNode != newRoot && showSubtree) {
						parentNode = parentNode.parent();
						if (SymbolicExecutionUtil.isTerminationNode(parentNode, parentNode.getAppliedRuleApp())) {
							if (getParent(parentNode) != getParent(node)) {
								termination = true;
							}
							break;
						} else if (isExecutionNode(parentNode)) {
							return -1;
						}
					}
				}
			}
			// test if parent node is in the symoblic execution tree
			if (SymbolicExecutionUtil.isTerminationNode(current, current.getAppliedRuleApp())) {
				termination = true;
			} else if (!(isExecutionNode(current) || termination)) {
				index = -1;
			}
		}
		// Find index of element
		boolean found = false;
		while (!found && current != null) {
			BranchFolder bf = branchFolders.get(current);
			if (showSubtree && current == newRoot) {
			   bf = null;
			}
			if (bf != null && bf != parent) {
				if (element == bf) {
					found = true;
				} else {
					Node parentNode = current.parent();
					int indexOnParent = parentNode.getChildNr(current);
					current = parentNode.child(indexOnParent + 1);
				}
			} else {
				if (element == current) {
					found = true;
				} else {
					if (current.childrenCount() != 1) {
						Node node;
						if (element instanceof BranchFolder) {
							node = ((BranchFolder) element).getChild();
						} else {
							node = (Node) element;
						}
						int childIndex = current.getChildNr(node);
						if (childIndex >= 0) {
							found = true;
							if (hideState) {
	                     index += childIndex;
							}
							else {
                        index += childIndex + 1;
							}
						} else {
							current = null; // Stop search, because element is
											// not a child of parent
						}
					} else {
						current = current.child(0);
						if (!hideState && !symbolicState) {
							index++;
						} else if (!hideState && symbolicState && (isExecutionNode(current) || termination)) {
							index++;
							if (SymbolicExecutionUtil.isTerminationNode(current, current.getAppliedRuleApp())) {
								termination = true;
							}
						}
					}
				}
			}
		}
		return found ? index : -1;
	}

	/**
	 * Returns the number of {@link BranchFolder} in Branch. This method can
	 * handle the inputs iff instanceof {@link Proof} or {@link BranchFolder}.
	 * 
	 * @param parent
	 *            - the parent object respectively the branches root.
	 * @return the number of {@link BranchFolder} in Branch
	 */
	protected int getFolderCountInBranch(Object parent) {
		if (parent instanceof Proof) {
			Proof proof = (Proof) parent;
			Node node = proof.root();
			if (showSubtree) {
			   node = newRoot;
			}
			while (node.childrenCount() == 1) {
				node = node.child(0);
			}
			return node.childrenCount();
		}
		else if (parent instanceof BranchFolder) {
			BranchFolder branchFolder = (BranchFolder) parent;
			Node node = branchFolder.getChild();
			while (node.childrenCount() == 1) {
				node = node.child(0);
			}
			return node.childrenCount();
		}
		else {
			return -1;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void dispose() {
		if (proof != null && !proof.isDisposed()) {
			proof.removeProofTreeListener(proofTreeListener);
		}
		if (pc != null) {
         pc.removeAutoModeListener(autoModeListener);
      }
	}
	
	public boolean getHideState(){
	   return hideState;
	}
	
	public void setHideState(boolean state){
		hideState = state;
	}
	
	public boolean getSymbolicState(){
		return symbolicState;
	}
	
	public void setSymbolicState(boolean state){
		symbolicState = state;
	}
	
	/**
	 * {@code true} if show subtree of node filter is turned on, {@code false} otherwise.
	 * @return {@code true} or {@code false}
	 */
	public boolean getShowSubtreeState() {
	   return showSubtree;
	}
	
	/**
	 * sets the state of the show subtree filter.
	 * @param state the boolean to set to
	 * @param rootNode the new root node 
	 */
	public void setShowSubtreeState(boolean state, Node rootNode) {
	   showSubtree = state;
	   newRoot = rootNode;
	}
	
	public boolean isExecutionNode(Node node) {
		if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, node.getAppliedRuleApp()) || node.root()) {
			return true;
		} else {
			return false;
		}
	}
}