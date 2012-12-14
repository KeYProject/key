package org.key_project.keyide.ui.providers;

import java.net.URL;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.key_project.util.java.ObjectUtil;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

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
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class OutlineLabelProvider extends LabelProvider {
   private Viewer viewer;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   private Proof proof;
   
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      @Override
      public void proofExpanded(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofPruned(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofClosed(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }

      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
         updateNodes(e); // TODO: Is this required, if not remove
      }      
   };
   
   
   private Map<Node, BranchFolder> nodeToBranchMapping = new HashMap<Node, BranchFolder>();
   
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         updateLeafs(e);
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
      }
   };
   
   public OutlineLabelProvider(Viewer viewer, KeYEnvironment<?> environment, Proof proof) {
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
   
   protected void updateLeafs(ProofEvent e) {
      // Iterate over complete tree to collect leaf branch folders because their label has to change if the branch was closed
      final List<Object> possibleChangedLeaves = new LinkedList<Object>();
      proof.breadthFirstSearch(proof.root(), new ProofVisitor() { // TODO: Implement event Goal removed in the future in KeY to remove this iteration with a direct backward iteration from the closed leaf node on which the goal wa removed.
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
                  fireLabelProviderChanged(new LabelProviderChangedEvent(OutlineLabelProvider.this, possibleChangedLeaves.toArray()));
               }
            }
         });
      }
   }

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
                        OutlineLabelProvider.this, changedParents.toArray()));
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
   //TODO: Images in SWT are C-Code. For this reason they should exist only once at runtime and they have to be disposed. They are also reusable. Implement a uitlity class like SEDImages (renamed into KeYIDEImages) which manages all images you need. Use its methods here.
   final Image FOLDER_IMAGE = getImageFromFile("icons/folder.png");

   final Image FOLDERPROVEN_IMAGE = getImageFromFile("icons/folderproved.png");


   final Image PROOF_IMAGE = getImageFromFile("icons/ekey-mono16.gif");
   
   final Image PROVEN_IMAGE = getImageFromFile("icons/keyproved16.gif");
   
   if(element instanceof Node){
      Node node = (Node)element;
      //((Node) element).proof()
      
      if(node.parent()!=null&&!node.root()){     
         if(node.name().equals("Closed goal")){
            return PROVEN_IMAGE;
         }
         return PROOF_IMAGE;
      }
   }
   if(element instanceof BranchFolder){
      if(((BranchFolder)element).isClosed()){
         return FOLDERPROVEN_IMAGE;
      }
      else {
         return FOLDER_IMAGE;
      }
   }
   return PROOF_IMAGE;
}

private static Image getImageFromFile(String file){
   Bundle bundle = FrameworkUtil.getBundle(OutlineLabelProvider.class);
   URL url = FileLocator.find(bundle, new Path(file), null);
   ImageDescriptor image = ImageDescriptor.createFromURL(url);
   return image.createImage();
}
   
}
