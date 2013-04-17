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
import java.util.Map;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A class to provide the proofTree transformed to the KeY-Internal representation.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan K�sdorf, Marco Drebing
 */
public class LazyProofTreeContentProvider implements ILazyTreeContentProvider{

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private Proof proof;
   private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();

   private TreeViewer viewer;
   
   /**
    * Flag which indicates that the viewer is currently refreshed when the auto mode has stopped.
    */
   private boolean refreshAfterAutoModeStopped = false;
   
   /**
    * The AutoModeListener
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         // TODO: Refactor functionality into LazyProofTreeContentProvider#handleAutoModeStopped(MouseEvent) which is called here
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            /**
             * {@inheritDoc}
             */
            @Override
            public void run() {
               try {
                  refreshAfterAutoModeStopped = true;
                  viewer.refresh(); // Refresh structure
                  viewer.refresh(); // Referesh labels and icons
               }
               finally {
                  refreshAfterAutoModeStopped = false;
               }
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void autoModeStarted(ProofEvent e) {
      }
   };
   
   
   /**
    * The ProofTreeListener
    */
   private ProofTreeListener proofTreeListener = new ProofTreeListener() {
      
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
      public void proofPruned(final ProofTreeEvent e) {
         // TODO: Refactor functionality into LazyProofTreeContentProvider#handleProofPruned(MouseEvent) which is called here
         if(!environment.getMediator().autoMode()){
            viewer.getControl().getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  prune(e.getNode());
               }
            });
         }
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
      public void proofGoalsAdded(final ProofTreeEvent e) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(final ProofTreeEvent e) {
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofExpanded(final ProofTreeEvent e) {
         // TODO: Refactor functionality into LazyProofTreeContentProvider#handleProofExpanded(MouseEvent) which is called here
         if(!environment.getMediator().autoMode()){
            viewer.getControl().getDisplay().asyncExec(new Runnable() {
               @Override
               public void run() {
                  viewer.refresh(); // TODO: Update viewer directly, will increase performance?
               }
            });
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofClosed(final ProofTreeEvent e) {
      }
   };


   /**
    * The Constructor
    * @param viewer - the {@link TreeViewer}
    * @param environment - the {@link KeYEnvironment}
    * @param proof - the {@link Proof}
    */
   public LazyProofTreeContentProvider(TreeViewer viewer, KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof){
      this.viewer=viewer;
      this.proof = proof;
      this.environment = environment;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      if(newInput instanceof Proof){
         this.proof = (Proof) newInput;
         if(oldInput != null){
            proof.removeProofTreeListener(proofTreeListener);
            if (environment != null) {
               environment.getMediator().removeAutoModeListener(autoModeListener);
            }
         }
          if(newInput != null){
             proof.addProofTreeListener(proofTreeListener);
          }
          if (environment != null) {
             environment.getMediator().addAutoModeListener(autoModeListener);
          }
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
         Node nonBranchingNode = (Node)element; 
         while (nonBranchingNode.parent() != null && nonBranchingNode.parent().childrenCount() == 1 ) {
            nonBranchingNode = nonBranchingNode.parent();
         }
         // Check if the root of the proof was found
         if (nonBranchingNode.parent() == null) {
            return proof;
         }
         else {
            // Get branch folder
            BranchFolder bf = branchFolders.get(nonBranchingNode);
            // Create branch folder if not available.
            if (bf == null) {
               bf = new BranchFolder(nonBranchingNode);
               branchFolders.put(nonBranchingNode, bf);
            }
            return bf;
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void updateChildCount(Object element, int currentChildCount) {
      if (element instanceof Proof){
         Proof proof = (Proof) element;
         Node branchNode = proof.root();
         int childCount = getBranchFolderChildCount(branchNode);
         int folderCount = getFolderCountInBranch(proof);
         viewer.setChildCount(element, childCount + folderCount);
      }
      if (element instanceof Node){
         viewer.setChildCount(element, 0);
      }
      if (element instanceof BranchFolder) {
         BranchFolder branchFolder = (BranchFolder) element;
         Node branchNode = branchFolder.getChild();
         int childCount = getBranchFolderChildCount(branchNode);
         int folderCount = getFolderCountInBranch(branchFolder);
         viewer.setChildCount(element, childCount + folderCount);
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
    * Removes the added listeners.
    */
   @Override
   public void dispose() {
      proof.removeProofTreeListener(proofTreeListener);
      environment.getMediator().removeAutoModeListener(autoModeListener);
   }
   
   
   private void prune(Node node){
      ISelection selection = viewer.getSelection(); // TODO: Content provider should do nothing with selection, find another way, maybe just use the node as element?
      if (selection instanceof TreeSelection){
         TreeSelection treeSelection = (TreeSelection) selection;
         Object element = treeSelection.getFirstElement();
         if (element instanceof BranchFolder){
            BranchFolder branchFolder = (BranchFolder) element;
            viewer.refresh(branchFolder);
         }
         else if (element instanceof Node){
            Node branchNode = getBranchNode((Node) element);
            BranchFolder branchFolder = branchFolders.get(branchNode);
            viewer.refresh(branchFolder);
         }
      }
   }
   
// private void prune(Node node){
// TreeViewerIterator it = new TreeViewerIterator(viewer);
// boolean notFound = true;
// TreeItem element;
// while(it.hasNext() && notFound){
//    element = it.next();
//    System.out.println(element.getData().g);
//    if(element.getData() instanceof BranchFolder){
//       if(((BranchFolder)element.getData()).getChild().equals(node)){
//          viewer.refresh(element);
//          notFound = false;
//       }
//    }
//    if(element.getData() instanceof Node){
//       if(element.getData().equals(node)){
//          viewer.refresh(element);
//          notFound = false;
//       }
//    }
// }
//}
   
   
   /**
    * Returns the number of {@link Node}s in the branch of the given {@link Node}. {@link BranchFolder}s in this branch will not be counted.
    * @param node - any {@link Node} out of the branch.
    * @return the number of {@link Node}s in the branch.
    */
   private int getBranchFolderChildCount(Node node){
      Node branchNode = getBranchNode(node);
      int count = 1;
      while(branchNode.childrenCount() == 1){
         branchNode = branchNode.child(0);
         count += 1;
      }
      return count;
   }


   /**
    * Returns the branch{@link Node} respectively the first child {@link Node} in its branch.
    * @param node - any {@link Node} out of the branch.
    * @return the branch{@link Node} respectively the first child {@link Node} in its branch.
    */
   private Node getBranchNode(Node node){
      if(node.equals(node.proof().root()))
         return node.proof().root();
      else if(node.parent().childrenCount() > 1)
         return node;
      else return getBranchNode(node.parent()); // TODO: Proof tree can be a very long which is not treatable with recursive method calls, use while loop instead
   }
   
   
   /**
    * Returns the element for the given parent and index. This method can handle the inputs iff instanceof {@link Proof} or {@link BranchFolder}.
    * @param parent - the parent object respectively the branches root.
    * @param index - the index of the element in its branch
    * @return the element for the given parent and index.
    */
   private Object getElementByIndex(Object parent, int index){
      Node node = null;
      int childCount = 0;
      if(parent instanceof Proof){
         Proof proof = (Proof) parent;
         node = proof.root();
         childCount = getBranchFolderChildCount(node);
      }
      else if(parent instanceof BranchFolder){
         BranchFolder branchFolder = (BranchFolder) parent;
         node = branchFolder.getChild();
         childCount = getBranchFolderChildCount(node);
      }
      //element is a Node
      if(index < childCount){
         for(int i = 0; i < index; i++){
            node = node.child(0);
         }
         return node; 
      }
      //element is a BranchFolder
      else{
         int folderIndex = index-childCount;
         for(int i = 0; i < childCount-1; i++){
            node = node.child(0);
         }
         BranchFolder branchFolder = new BranchFolder(node.child(folderIndex));
         branchFolders.put(node.child(folderIndex), branchFolder);
         return branchFolder;
      }
   }

   /**
    * Returns the index of the given element at its given parent.
    * @param parent The parent to search in.
    * @param element The element to compute its child index.
    * @return The child index of the element or {@code -1} if it is not a child of the parent.
    */
   public int getIndexOf(Object parent, Object element) {
      // Find first shown child node of the given parent
      Node current = null;
      if (parent instanceof Proof) {
         current = ((Proof) parent).root();
      }
      else if (parent instanceof BranchFolder) {
         current = ((BranchFolder) parent).getChild();
      }
      // Find index of element
      int index = 0;
      boolean found = false;
      while (!found && current != null) {
         BranchFolder bf = branchFolders.get(current);
         if (bf != null && bf != parent) {
            if (element == bf) {
               found = true;
            }
            else {
               Node parentNode = current.parent();
               int indexOnParent = parentNode.getChildNr(current);
               current = parentNode.child(indexOnParent + 1);
               index++;
            }
         }
         else {
            if (element == current) {
               found = true;
            }
            else {
               if(current.childrenCount()==0&&current.parent().childrenCount()==2){
                  current=current.parent().child(1);
                  index++;
               }else{
                  current = current.child(0);
                  index++;
               }
            }
         }
      }
      return found ? index : -1;
   }
   
   /**
    * Returns the number of {@link BranchFolder} in Branch. This method can handle the inputs iff instanceof {@link Proof} or {@link BranchFolder}.
    * @param parent - the parent object respectively the branches root.
    * @return the number of {@link BranchFolder} in Branch
    */
   //Returns the number of folders in a branch.
   private int getFolderCountInBranch(Object parent){
      if(parent instanceof Proof){
         Proof proof = (Proof) parent;
         Node node = proof.root();
         while(node.childrenCount()==1){
            node = node.child(0);
         }
         return node.childrenCount();
      }
      else if(parent instanceof BranchFolder){
         BranchFolder branchFolder = (BranchFolder) parent;
         Node node = branchFolder.getChild();
         while(node.childrenCount()==1){
            node = node.child(0);
         }
         return node.childrenCount();
      }
      else return -1;
   }
   
   
   /**
    * Checks if the viewer is currently refreshed after stopping the auto mode. 
    * @return {@code true} in refresh phase, {@code false} not in refresh phase.
    */
   public boolean isRefreshAfterAutoModeStopped() {
      return refreshAfterAutoModeStopped;
   }   
}