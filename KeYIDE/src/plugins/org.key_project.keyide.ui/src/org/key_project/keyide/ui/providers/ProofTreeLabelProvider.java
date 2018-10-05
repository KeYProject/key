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

import java.util.*;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.BlockContractValidityTermLabel;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The {@link LabelProvider} used to label a proof tree consiting of 
 * {@link Proof}s, {@link Node}s and {@link BranchFolder}s.
 * @author Martin Hentschel
 */
public class ProofTreeLabelProvider extends LabelProvider {
   /**
    * The {@link Viewer} in which this {@link LabelProvider} is used.
    */
   private final Viewer viewer;
   
   /**
    * The {@link ProofControl} to use.
    */
   private final ProofControl proofControl;
   
   /**
    * The shown {@link Proof} as root of the proof tree.
    */
   private final Proof proof;
   
   /**
    * A mapping from {@link Node}s to {@link BranchFolder}s.
    */
   private final Map<Node, BranchFolder> nodeToBranchMapping = new HashMap<Node, BranchFolder>();
   
   /**
    * The ProofTreeListener
    */
   private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofPruned(ProofTreeEvent e) {
         hanldeProofPruned(e);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         handleProofGoalAdded(e);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         handleProofGoalRemoved(e);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofExpanded(ProofTreeEvent e) {
         handleProofExpanded(e);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofClosed(ProofTreeEvent e) {
         handleProofClosed(e);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void notesChanged(ProofTreeEvent e) {
         handleNotesChanged(e);
      }
   };
   
   /**
    * Listens for changes on {@link Goal}s.
    */
   private final GoalListener goalListener = new GoalListener() {
      @Override
      public void sequentChanged(Goal source, SequentChangeInfo sci) {
      }

      @Override
      public void goalReplaced(Goal source, Node parent, ImmutableList<Goal> newGoals) {
      }

      @Override
      public void automaticStateChanged(Goal source, boolean oldAutomatic, boolean newAutomatic) {
         handleAutomaticStateChanged(source, oldAutomatic, newAutomatic);
      }
   };
   
   /**
    * All observed {@link Goal}s.
    */
   private final Set<Goal> observedGoals = new HashSet<Goal>();
   
   /**
    * Listens for auto mode start and stop events.
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
    * The Constructor
    * @param viewer The {@link Viewer} in which this {@link LabelProvider} is used.
    * @param proofControl The {@link ProofControl} to use.
    * @param proof The shown {@link Proof} as root of the proof tree.
    */
   public ProofTreeLabelProvider(Viewer viewer, ProofControl proofControl, Proof proof) {
      this.viewer = viewer;
      this.proofControl = proofControl;
      this.proof = proof;
      if (proof != null && !proof.isDisposed()) {
         proof.addProofTreeListener(proofTreeListener);
         proofControl.addAutoModeListener(autoModeListener);
         for (Goal goal : proof.openGoals()) {
            if (observedGoals.add(goal)) {
               goal.addGoalListener(goalListener);
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element){
      if(element instanceof Node) {
         Node node = (Node)element;
         return getNodeText(node);
      }
      else if(element instanceof BranchFolder){
         BranchFolder folder = (BranchFolder)element;
         nodeToBranchMapping.put(folder.getChild(), folder);
         return folder.getLabel(); 
      }
      else {
         return ObjectUtil.toString(element);
      }
   }
   
   /**
    * Returns the text to show for the given {@link Node}.
    * @param node The {@link Node} for which the text is requested.
    * @return The text of the node to show.
    */
   public static String getNodeText(Node node) {
      if (node.childrenCount() == 1) {
         Node child = node.child(0);
         if (child.getNodeInfo().getBranchLabel() != null) {
            return node.serialNr() + ":" + node.name() + ": " + child.getNodeInfo().getBranchLabel();
         }
         else {
            return node.serialNr() + ":" + node.name();
         }
      }
      else {
         return node.serialNr() + ":" + node.name();
      }
   }
   
	/**
	 * {@inheritDoc}
	 */
	@Override
	public Image getImage(Object element) {
		if (element instanceof Node) {
			Node node = (Node) element;
			NodeInfo info = node.getNodeInfo();
			SourceElement statement = info.getActiveStatement();
			if (node.isClosed()) {
				return KeYImages.getImage(KeYImages.NODE_PROVED);
			}
			else if (node.leaf()) {
			   Goal goal = node.proof().getGoal(node);
			   if (goal != null && goal.isAutomatic()) {
	            return KeYImages.getImage(KeYImages.NODE);
			   }
			   else {
	            return KeYImages.getImage(KeYImages.DISABLED_GOAL);
			   }
			}
			else if (node.root()) {
				return KeYImages.getImage(KeYImages.THREAD);
			}
			else if (SymbolicExecutionUtil.isSymbolicExecutionTreeNode(node, node.getAppliedRuleApp())) {
				// Get position information
				PositionInfo posInfo = null;
				if (statement != null) {
					posInfo = statement.getPositionInfo();
				}
				if (SymbolicExecutionUtil.isBlockSpecificationElement(node, node.getAppliedRuleApp())) {
				   if (node.childrenCount() >= 3 && node.child(1).isClosed()) {
				      return KeYImages.getImage(KeYImages.BLOCK_CONTRACT);
				   }
				   else {
                  return KeYImages.getImage(KeYImages.BLOCK_CONTRACT_NOT_PRE);
				   }
				}
				else if (SymbolicExecutionUtil.isMethodCallNode(node, node.getAppliedRuleApp(), statement)) {
					return KeYImages.getImage(KeYImages.METHOD_CALL);

				}
				else if (SymbolicExecutionUtil.isMethodReturnNode(node, node.getAppliedRuleApp())) {
					return KeYImages.getImage(KeYImages.METHOD_RETURN);

				}
				else if (SymbolicExecutionUtil.isExceptionalMethodReturnNode(node, node.getAppliedRuleApp())) {
					return KeYImages.getImage(KeYImages.EXCEPTIONAL_METHOD_RETURN);

				}
				else if (SymbolicExecutionUtil.isTerminationNode(node, node.getAppliedRuleApp())) {
               if (SymbolicExecutionUtil.isBlockContractValidityBranch(node.getAppliedRuleApp())) {
                  Term modalityTerm = TermBuilder.goBelowUpdates(node.getAppliedRuleApp().posInOccurrence().subTerm());
                  BlockContractValidityTermLabel bcLabel = (BlockContractValidityTermLabel) modalityTerm.getLabel(BlockContractValidityTermLabel.NAME);
                  if (SymbolicExecutionUtil.lazyComputeIsExceptionalTermination(node, 
                          (IProgramVariable) MiscTools.findActualVariable(bcLabel.getExceptionVariable(), node))) {
                     if (SymbolicExecutionUtil.lazyComputeIsAdditionalBranchVerified(node)) {
                        return KeYImages.getImage(KeYImages.BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION);
                     }
                     else {
                        return KeYImages.getImage(KeYImages.BLOCK_CONTRACT_EXCEPTIONAL_TERMINATION_NOT_VERIFIED);
                     }
                  }
                  else {
                     if (SymbolicExecutionUtil.lazyComputeIsAdditionalBranchVerified(node)) {
                        return KeYImages.getImage(KeYImages.BLOCK_CONTRACT_TERMINATION);
                     }
                     else {
                        return KeYImages.getImage(KeYImages.BLOCK_CONTRACT_TERMINATION_NOT_VERIFIED);
                     }
                  }
               }
               else if (SymbolicExecutionUtil.isLoopBodyTermination(node, node.getAppliedRuleApp())) {
						if (SymbolicExecutionUtil.lazyComputeIsMainBranchVerified(node)) {
							return KeYImages.getImage(KeYImages.LOOP_BODY_TERMINATION);
						}
						else {
							return KeYImages.getImage(KeYImages.LOOP_BODY_TERMINATION_NOT_VERIFIED);
						}
					}
               else if (SymbolicExecutionUtil.lazyComputeIsExceptionalTermination(node, SymbolicExecutionUtil.extractExceptionVariable(node.proof()))) {
                  if (SymbolicExecutionUtil.lazyComputeIsMainBranchVerified(node)) {
                     return KeYImages.getImage(KeYImages.EXCEPTIONAL_TERMINATION);
                  }
                  else {
                     return KeYImages.getImage(KeYImages.EXCEPTIONAL_TERMINATION_NOT_VERIFIED);
                  }
					}
               else {
                  if (SymbolicExecutionUtil.lazyComputeIsMainBranchVerified(node)) {
                     return KeYImages.getImage(KeYImages.TERMINATION);
                  }
                  else {
                     return KeYImages.getImage(KeYImages.TERMINATION_NOT_VERIFIED);
                  }
					}
				}
				else if (SymbolicExecutionUtil.isBranchStatement(node, node.getAppliedRuleApp(), statement, posInfo)) {
					return KeYImages.getImage(KeYImages.BRANCH_STATEMENT);
				}
				else if (SymbolicExecutionUtil.isLoopStatement(node, node.getAppliedRuleApp(), statement, posInfo)) {
					return KeYImages.getImage(KeYImages.LOOP_STATEMENT);
				}
				else if (SymbolicExecutionUtil.isStatementNode(node, node.getAppliedRuleApp(), statement, posInfo)) {
					return KeYImages.getImage(KeYImages.STATEMENT);
				}
				else if (SymbolicExecutionUtil.isOperationContract(node, node.getAppliedRuleApp())) {
					// is precondition compiled
					if (node.childrenCount() >= 3 && node.child(2).isClosed()) {
						// is not null check compiled
						if (node.childrenCount() >= 4 && node.child(3).isClosed()) {
							return KeYImages.getImage(KeYImages.METHOD_CONTRACT);
						}
						else {
							return KeYImages.getImage(KeYImages.METHOD_CONTRACT_NOT_NPC);
						}
					}
					else {
						// is not null check compiled
						if (node.childrenCount() >= 4 && node.child(3).isClosed()) {
							return KeYImages.getImage(KeYImages.METHOD_CONTRACT_NOT_PRE);
						}
						else {
							return KeYImages.getImage(KeYImages.METHOD_CONTRACT_NOT_PRE_NOT_NPC);
						}
					}
				}
				else if (SymbolicExecutionUtil.hasLoopCondition(node, node.getAppliedRuleApp(), statement)) {
					return KeYImages.getImage(KeYImages.LOOP_CONDITION);
				}
				else if (SymbolicExecutionUtil.isLoopInvariant(node, node.getAppliedRuleApp())) {
					// is initially valid
					if (node.childrenCount() >= 1 && node.child(0).isClosed()) {
						return KeYImages.getImage(KeYImages.LOOP_INVARIANT);
					}
					else {
						return KeYImages.getImage(KeYImages.LOOP_INVARIANT_INITIALLY_INVALID);
					}
				}
				else {
					return KeYImages.getImage(KeYImages.NODE);
				}
			}
			else {
				if (node.getNodeInfo().getInteractiveRuleApplication()) {
					return KeYImages.getImage(KeYImages.NODE_INTERACTIVE);
				}
				else {
					return KeYImages.getImage(KeYImages.NODE);
				}
			}
		}
		else if (element instanceof BranchFolder) {
			if (((BranchFolder) element).isClosed()) {
				return KeYImages.getImage(KeYImages.FOLDER_PROVED);
			}
			else {
				return KeYImages.getImage(KeYImages.FOLDER);
			}
		}
		else {
			return super.getImage(element); // Unknown element
		}
	}

   /**
    * When the auto mode is started.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStopped(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.addProofTreeListener(proofTreeListener);
      }
      fireAllNodesChanged();
   }

   /**
    * When the auto mode has finished.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      if (proof != null && !proof.isDisposed()) {
         proof.removeProofTreeListener(proofTreeListener);
      }
   }

   /**
    * When a {@link Node} was expanded.
    * @param e The event.
    */
   protected void handleProofExpanded(final ProofTreeEvent e) {
      fireNodeChanged(e.getNode());
   }

   /**
    * When the automatic state of a {@link Goal} has changed.
    * @param source The changed {@link Goal}.
    * @param oldAutomatic The old state.
    * @param newAutomatic The new state.
    */
   protected void handleAutomaticStateChanged(Goal source, boolean oldAutomatic, boolean newAutomatic) {
      fireNodeChanged(source.node());
   }
   
   /**
    * When a {@link Proof} is closed.
    * @param e The event.
    */
   protected void handleProofClosed(ProofTreeEvent e) {
      fireAllNodesChanged();
   }

   /**
    * When a {@link Node} was pruned.
    * @param e The event.
    */
   protected void hanldeProofPruned(final ProofTreeEvent e) {
      fireNodeChanged(e.getNode());
   }

   /**
    * When the notes of a {@link Node} have changed.
    * @param e The event.
    */
   protected void handleNotesChanged(ProofTreeEvent e) {
      fireNodeChanged(e.getNode());
   }

   /**
    * When a {@link Goal} is added.
    * @param e The event.
    */
   protected void handleProofGoalAdded(ProofTreeEvent e) {
      if (e.getGoal() != null) {
         if (observedGoals.add(e.getGoal())) {
            e.getGoal().addGoalListener(goalListener);
         }
      }
      if (e.getGoals() != null && !e.getGoals().isEmpty()) {
         for (Goal goal : e.getGoals()) {
            if (observedGoals.add(goal)) {
               goal.addGoalListener(goalListener);
            }
         }
      }
      handleProofGoalRemovedOrAdded(e);
   }

   /**
    * When a {@link Goal} is removed.
    * @param e The event.
    */
   protected void handleProofGoalRemoved(ProofTreeEvent e) {
      if (e.getGoal() != null) {
         if (observedGoals.remove(e.getGoal())) {
            e.getGoal().removeGoalListener(goalListener);
         }
      }
      if (e.getGoals() != null && !e.getGoals().isEmpty()) {
         for (Goal goal : e.getGoals()) {
            if (observedGoals.remove(goal)) {
               goal.removeGoalListener(goalListener);
            }
         }
      }
      handleProofGoalRemovedOrAdded(e);
   }

   /**
    * When a {@link Goal} is added or removed.
    * @param e The event.
    */
   protected void handleProofGoalRemovedOrAdded(ProofTreeEvent e) {
      if (e.getGoal() != null) {
         fireNodeChanged(e.getGoal().node());
      }
      else if (e.getGoals() != null && !e.getGoals().isEmpty()) {
         List<Node> nodes = new ArrayList<Node>(e.getGoals().size());
         for (Goal goal : e.getGoals()) {
            nodes.add(goal.node());
         }
         fireNodesChanged(nodes.toArray(new Node[nodes.size()]));
      }
      else {
         fireAllNodesChanged();
      }
   }
   
   /**
    * Fires the event that all {@link Node}s have changed.
    */
   protected void fireAllNodesChanged() {
      if (!viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(ProofTreeLabelProvider.this));
               }
            }
         });
      }
   }
   
   /**
    * Fires the event that the given {@link Node} has changed.
    * @param node The changed {@link Node}.
    */
   protected void fireNodeChanged(final Node node) {
      if (!viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(ProofTreeLabelProvider.this, node));
               }
            }
         });
      }
   }
   
   /**
    * Fires the event that the given {@link Node}s have changed.
    * @param nodes The changed {@link Node}s.
    */
   protected void fireNodesChanged(final Node... nodes) {
      if (!viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().syncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(ProofTreeLabelProvider.this, nodes));
               }
            }
         });
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proof != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
      if (proofControl != null) {
         proofControl.removeAutoModeListener(autoModeListener);
      }
      for (Goal goal : observedGoals) {
         goal.removeGoalListener(goalListener);
      }
      observedGoals.clear();
      super.dispose();
   }    
}