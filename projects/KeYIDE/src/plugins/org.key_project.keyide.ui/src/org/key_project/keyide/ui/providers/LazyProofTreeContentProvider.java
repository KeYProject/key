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

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

/**
 * A class to provide the proofTree transformed to the KeY-Internal representation.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class LazyProofTreeContentProvider implements ILazyTreeContentProvider {
   /**
    * A mapping from {@link Node}s to {@link BranchFolder}s.
    */   
   private final Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();
   
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
         handleProofPruned(e);
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
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
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
      }
   };

   /**
    * The {@link TreeViewer} in which this {@link ILazyTreeContentProvider} is used.
    */
   private TreeViewer viewer;
   
   /**
    * The {@link Proof} as input of {@link #viewer}.
    */
   private Proof proof;   

   /**
    * The Constructor
    */
   public LazyProofTreeContentProvider() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      Assert.isTrue(viewer instanceof TreeViewer);
      this.viewer = (TreeViewer)viewer;
      if (oldInput != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
      if (newInput instanceof Proof) {
         this.proof = (Proof) newInput;
         proof.addProofTreeListener(proofTreeListener);
      }
      else {
         this.proof = null;
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
      doUpdateChildCount(element, currentChildCount);
   }
   
   /**
    * Performs the steps of {@link #updateChildCount(Object, int)}.
    * @param element The element to update its child count.
    * @param currentChildCount The current number of children.
    * @return The new updated number of children.
    */
   protected int doUpdateChildCount(Object element, int currentChildCount) {
      if (element instanceof Proof){
         Proof proof = (Proof) element;
         Node branchNode = proof.root();
         int childCount = getBranchFolderChildCount(branchNode);
         int folderCount = getFolderCountInBranch(proof);
         viewer.setChildCount(element, childCount + folderCount);
         return childCount + folderCount;
      }
      if (element instanceof Node){
         viewer.setChildCount(element, 0);
         return 0;
      }
      if (element instanceof BranchFolder) {
         BranchFolder branchFolder = (BranchFolder) element;
         Node branchNode = branchFolder.getChild();
         int childCount = getBranchFolderChildCount(branchNode);
         int folderCount = getFolderCountInBranch(branchFolder);
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
    * @param e The event.
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
    * @param node The expanded {@link Node}.
    */
   protected void doHandleProofPruned(Node node){
      doUpdateChildCount(getParent(node), -1);
   }

   /**
    * When a {@link Node} was expanded.
    * @param e The event.
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
    * @param node The expanded {@link Node}.
    */
   protected void doHandleProofExpanded(Node node) {
      Object parent = getParent(node);
      int parentChildCount = doUpdateChildCount(parent, -1);
      int childIndex = getIndexOf(parent, node);
      if (childIndex >= 0 && childIndex < parentChildCount) {
         for (int i = childIndex; i < parentChildCount; i++) {
            updateElement(parent, i);
         }
      }
   }
   
   /**
    * Returns the number of {@link Node}s in the branch of the given {@link Node}. {@link BranchFolder}s in this branch will not be counted.
    * @param node - any {@link Node} out of the branch.
    * @return the number of {@link Node}s in the branch.
    */
   protected int getBranchFolderChildCount(Node node){
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
   protected Node getBranchNode(Node node){
      while(true){
         if(node.equals(node.proof().root())  || node.parent().childrenCount() > 1){
            return node;
         }
         else{
            node = node.parent();
         }
      }
   }
   
   /**
    * Returns the element for the given parent and index. This method can handle the inputs iff instanceof {@link Proof} or {@link BranchFolder}.
    * @param parent - the parent object respectively the branches root.
    * @param index - the index of the element in its branch
    * @return the element for the given parent and index.
    */
   protected Object getElementByIndex(Object parent, int index){
      Node node = null;
      int childCount = 0;
      if (parent instanceof ContributionInfo) {
         node = proof.root();
         childCount = getBranchFolderChildCount(node);
      }
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
      // Make sure that parameters are valid
      Assert.isTrue(element instanceof BranchFolder || element instanceof Node, "Unsupported element \"" + element + "\".");
      Assert.isTrue(parent instanceof Proof || parent instanceof BranchFolder || parent instanceof Node, "Unsupported parent \"" + parent + "\".");
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
               if (current.childrenCount() != 1) {
                  Node node;
                  if (element instanceof BranchFolder) {
                     node = ((BranchFolder) element).getChild();
                  }
                  else {
                     node = (Node)element;
                  }
                  int childIndex = current.getChildNr(node);
                  if (childIndex >= 0) {
                     found = true;
                     index += childIndex + 1;
                  }
                  else {
                     current = null; // Stop search, because element is not a child of parent
                  }
               }
               else {
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
   protected int getFolderCountInBranch(Object parent){
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
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proof != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
   }
}