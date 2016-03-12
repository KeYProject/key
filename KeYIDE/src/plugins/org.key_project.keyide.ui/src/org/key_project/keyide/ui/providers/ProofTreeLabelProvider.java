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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

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
   private final ProofTreeListener proofTreeListener = new ProofTreeListener() {
      /**
       * {@inheritDoc}
       */
      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
      }
      
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
      public void proofIsBeingPruned(ProofTreeEvent e) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         handleProofGoalRemovedOrAdded(e);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         handleProofGoalRemovedOrAdded(e);
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
   };
   
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
      if (proof != null) {
         proof.addProofTreeListener(proofTreeListener);
         proofControl.addAutoModeListener(autoModeListener);
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
      if (element instanceof Node){
         Node node = (Node)element;
         if (node.isClosed()) {
            return KeYImages.getImage(KeYImages.NODE_PROVED);
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
      else if (element instanceof BranchFolder){
         if (((BranchFolder)element).isClosed()){
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
      proof.addProofTreeListener(proofTreeListener);
      fireAllNodesChanged();
   }

   /**
    * When the auto mode has finished.
    * @param e The {@link ProofEvent}.
    */
   protected void handleAutoModeStarted(ProofEvent e) {
      proof.removeProofTreeListener(proofTreeListener);
   }

   /**
    * When a {@link Node} was expanded.
    * @param e The event.
    */
   protected void handleProofExpanded(final ProofTreeEvent e) {
      fireNodeChanged(e.getNode());
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
      super.dispose();
   }    
}