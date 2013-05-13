/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A class to provide the correct labels for the KeY-Outline.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing, Martin Hentschel
 */
public class ProofTreeLabelProvider extends LabelProvider {
   private Viewer viewer;
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private Proof proof;
   private Map<Node, BranchFolder> nodeToBranchMapping = new HashMap<Node, BranchFolder>();
   
   /**
    * The ProofTreeListener
    */
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      @Override
      public void proofExpanded(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofPruned(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofClosed(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
//         updateNodes(e); // TODO: Is this required, if not remove
      }      
   };
   
   /**
    * The AutoModeListener
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         updateLeafs(e);
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
      }
   };
   
   
   /**
    * The Constructor
    * @param viewer
    * @param environment
    * @param proof
    */
   // TODO Comment
   public ProofTreeLabelProvider(Viewer viewer, KeYEnvironment<?> environment, Proof proof) {
      super();
      this.viewer = viewer;
      this.proof = proof;
      if (proof != null) {
         proof.addProofTreeListener(proofTreeListener);
      }
      if (environment != null) {
         environment.getMediator().addAutoModeListener(autoModeListener);
      }
   }
   
   /**
    * Iterates over the complete tree and collects leaf branch folders because their label has to change if the branch was closed.
    * @param e - {@link ProofEvent}
    */
   protected void updateLeafs(ProofEvent e) { // TODO: Should this method not be called also when a rule is applied manually? Or in general an event thrown? If not remove proofTreeListener
      final List<Object> possibleChangedLeaves = new LinkedList<Object>();
      proof.breadthFirstSearch(proof.root(), new ProofVisitor() { // TODO: Implement event Goal removed in the future in KeY to remove this iteration with a direct backward iteration from the closed leaf node on which the goal was removed.
         @Override
         public void visit(Proof proof, Node visitedNode) {
            if (visitedNode.isClosed()) {
               BranchFolder visitedNodeBF = nodeToBranchMapping.get(visitedNode);
               if (visitedNodeBF != null) {
                  possibleChangedLeaves.add(visitedNodeBF);
               }               
            }
         }
      });
      // Inform viewer about changed objects to update texts and images
      if (!possibleChangedLeaves.isEmpty() && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(ProofTreeLabelProvider.this, possibleChangedLeaves.toArray()));
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
      super.dispose();
      if (proof != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
      if (environment != null) {
         environment.getMediator().removeAutoModeListener(autoModeListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element){
      if(element instanceof Node) {
         Node node = (Node)element;
         // Return text to show
         if(node.childrenCount() == 1) {
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
            return KeYImages.getImage(KeYImages.NODE);
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
}