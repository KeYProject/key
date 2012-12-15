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
import de.uka.ilkd.key.proof.Goal;
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
   protected void updateLeafs(ProofEvent e) {
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
    * 
    * @param e - {@link ProofTreeEvent}
    */
   protected void updateNodes(final ProofTreeEvent e) {
      // Collect changed objects in event
      final List<Object> changedParents = new LinkedList<Object>();
      if (e.getGoals() != null) {
         boolean multipleGoals = e.getGoals().size() >= 2;
         for (Goal goal : e.getGoals()) {
            Node node = goal.node();
            if (!multipleGoals && node.parent() != null
                  && node.getNodeInfo().getBranchLabel() != null) {
               // Add also parent node to changed objects because in case of
               // OneStepSimplification the number of applied rules is shown as
               // branch label on it
               changedParents.add(goal.node().parent());
            }
            changedParents.add(node);
            BranchFolder bf = nodeToBranchMapping.get(node);
            if (bf != null) {
               changedParents.add(bf);
            }
         }
      }
      // Inform viewer about changed objects to update texts and images
      if (!changedParents.isEmpty() && !viewer.getControl().isDisposed()) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!viewer.getControl().isDisposed()) {
                  fireLabelProviderChanged(new LabelProviderChangedEvent(
                        ProofTreeLabelProvider.this, changedParents.toArray()));
               }
            }
         });
      }
   }

   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      final Image FOLDER_IMAGE = KeYImages.getImage("org.key_project.keyide.ui.images.folder");
      final Image FOLDER_PROVED_IMAGE = KeYImages.getImage("org.key_project.keyide.ui.images.folderProved");
      final Image NODE_IMAGE = KeYImages.getImage("org.key_project.keyide.ui.images.node");
      final Image NODE_PROVED_IMAGE = KeYImages.getImage("org.key_project.keyide.ui.images.nodeProved");
      
      if(element instanceof Node){
         Node node = (Node)element;
         if(node.parent()!=null&&!node.root()){     
            if(node.name().equals("Closed goal")){
               return NODE_PROVED_IMAGE;
            }
            return NODE_IMAGE;
         }
      }
      if(element instanceof BranchFolder){
         if(((BranchFolder)element).isClosed()){
            return FOLDER_PROVED_IMAGE;
         }
         else {
            return FOLDER_IMAGE;
         }
      }
      return NODE_IMAGE;
   }
      
}
