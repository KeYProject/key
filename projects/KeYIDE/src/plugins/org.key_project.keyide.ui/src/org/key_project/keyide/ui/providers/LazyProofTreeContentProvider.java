package org.key_project.keyide.ui.providers;


import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

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
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class LazyProofTreeContentProvider implements ILazyTreeContentProvider{

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private Proof proof;
   private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();

   private TreeViewer viewer;
   
   
   /**
    * The Constructor
    * @param viewer - the {@link TreeViewer}
    * @param environment - the {@link KeYEnvironment}
    * @param proof - the {@link Proof}
    */
   public  LazyProofTreeContentProvider(TreeViewer viewer, KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof){
      this.viewer=viewer;
      this.proof = proof;
      this.environment = environment;
   }
   
   
   /**
    * The AutoModeListener
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            
            /**
             * {@inheritDoc}
             */
            @Override
            public void run() {
               viewer.refresh();
               viewer.refresh();

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
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofPruned(final ProofTreeEvent e) {
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
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsAdded(final ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(final ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofExpanded(final ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
         Display.getDefault().asyncExec(new Runnable() {
            
            /**
             * {@inheritDoc}
             */
            @Override
            public void run() {
            }
            
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofClosed(final ProofTreeEvent e) {
         if(!environment.getMediator().autoMode()){
         }
      }
   };
   

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
      if(element instanceof Node){
         Node node = (Node) element;
         Node branchNode = getBranchNode(node);
         if(node.equals(branchNode)){
            return branchFolders.get(node);
         }
         else{
            return node.parent();
         }
      }
      else if(element instanceof BranchFolder){
         BranchFolder branchFolder = (BranchFolder) element;
         return branchFolder.getChild().parent();
      }
      else return null;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void updateChildCount(Object element, int currentChildCount) {
      if(element instanceof Proof){
         Proof proof = (Proof) element;
         Node branchNode = proof.root();
         int childCount = getBranchFolderChildCount(branchNode);
         int folderCount = getFolderCountInBranch(proof);
         viewer.setChildCount(element, childCount + folderCount);
      }
      if(element instanceof Node){
         viewer.setChildCount(element, 0);
      }
      if(element instanceof BranchFolder) {
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
      refreshSelection(element);         
      updateChildCount(element, -1);
   }
   
   /**
    * 
    * @param element - a {@link Node} or a {@link BranchFolder}
    */
   
   private void refreshSelection(Object element){
      ISelection selection = viewer.getSelection();
      if(selection.isEmpty()){
         viewer.getTree().setSelection(viewer.getTree().getItem(0));
         viewer.setSelection(viewer.getSelection(), true);
         
      }
      else if(selection instanceof TreeSelection){
         TreeSelection treeSelection = (TreeSelection) selection;
         if(treeSelection.getFirstElement().equals(element)){
            viewer.setSelection(viewer.getSelection());
         }
      }
   }
   
   
   /**
    * Removes the added listeners.
    */
   @Override
   public void dispose() {
      proof.removeProofTreeListener(proofTreeListener);
      environment.getMediator().removeAutoModeListener(autoModeListener);
   }


   /**
    * Creates the required {@link BranchFolder}s for the given {@link Node}. Ensure that the {@link Node} is the last {@link Node} of its branch and that it has more then one child {@link Node}.
    * @param node - the last {@link Node} of a branch.
    */
   private void createFolder(Node node){
      for(int i = 0; i < node.childrenCount(); i++){
         BranchFolder parentBranchFolder = getBranchFolder(node);
         BranchFolder branchFolder = new BranchFolder(node.child(i));
         branchFolders.put(node.child(i), branchFolder);
         int nodeIndex = getNodeIndexInBranch(node);
         if(parentBranchFolder == null)
            viewer.replace(node.proof(), nodeIndex+i+1, branchFolder);
         else
            viewer.replace(parentBranchFolder, nodeIndex+i+1, branchFolder);
         viewer.setChildCount(branchFolder, 1);
         viewer.replace(branchFolder,0 , node.child(i));
      }
   }
   
   
   private void prune(Node node){
      ISelection selection = viewer.getSelection();
      if(selection instanceof TreeSelection){
         TreeSelection treeSelection = (TreeSelection) selection;
         Object element = treeSelection.getFirstElement();
         if(element instanceof BranchFolder){
            BranchFolder branchFolder = (BranchFolder) element;
            viewer.refresh(branchFolder);
         }
         else if(element instanceof Node){
            Node branchNode = getBranchNode((Node) element);
            BranchFolder branchFolder = branchFolders.get(branchNode);
            viewer.refresh(branchFolder);
         }
      }
   }
   

   /**
    * Manages the whole tree expansion by calling the specified method for the given {@link Node}.
    * @param node - the {@link Node} that has to be expanded.
    */
   @SuppressWarnings("unused")
   private void expanded(Node node){
      if(isBranchNodeRoot(node)){
         expandedRoot(node);
      }
      else expandedFolder(node);
   }
   
   
   /**
    * Manages the expansion of the tree when the branch root of the given {@link Node} is a {@link BranchFolder}. 
    * @param node - the {@link Node} that has to be expanded.
    */
   private void expandedFolder(Node node){
      BranchFolder branchFolder = getBranchFolder(node);
      int index = getNodeIndexInBranch(node);
      int size = getBranchFolderChildCount(node);
      viewer.setChildCount(branchFolder, size);
      viewer.replace(branchFolder, index, node);
      if(index == size-2 && node.childrenCount() == 1){       
         viewer.replace(branchFolder, index+1, node.child(0));
      }
      else if(index == size-1 && node.childrenCount() > 1){
         createFolder(node);
      }
   }


   /**
    * Manages the expansion of the tree when the branch root of the given {@link Node} is a {@link Proof}.
    * @param node - the {@link Node} that has to be expanded.
    */
   private void expandedRoot(Node node){
      int index = getNodeIndexInBranch(node);
      int size = getBranchFolderChildCount(node);
      viewer.setChildCount(node.proof(), size);
      viewer.replace(node.proof(), index, node);
      
      if(index == size-2 && node.childrenCount() == 1){
         viewer.replace(node.proof(), index+1, node.child(0));
      }
      else if(index == size-1 && node.childrenCount() > 1){
         viewer.setChildCount(node.proof(), size+node.childrenCount());
         createFolder(node);
      }
   }


   /**
    * Returns the {@link BranchFolder} of the given {@link Node}.
    * @param node - any {@link Node out of a branch}
    * @return the {@link BranchFolder} of the given {@link Node}. Null if the branchFolder of the branch is the {@link Proof}.
    */
   private BranchFolder getBranchFolder(Node node){
      Node branchNode = getBranchNode(node);
      if(branchNode.equals(node.proof().root()))
         return null;
      else
         return branchFolders.get(branchNode);
   }
   
   
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
      else return getBranchNode(node.parent());
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
    * Returns the index of the given {@link Node} in its branch.
    * @param node - any node of a branch.
    * @return the index of the given {@link Node} in its branch.
    */
   private int getNodeIndexInBranch(Node node){
      Node branchNode = getBranchNode(node);
      int count = 0;
      while(!node.equals(branchNode) && branchNode.childrenCount() == 1){
         branchNode = branchNode.child(0);
         count += 1;
      }
      return count;
   }
   
   
   /**
    * Returns true iff the branch{@link Node} of the given {@link Node} is the {@link Proof}s root{@link Node}. Else false.
    * @param node - any node of a branch
    * @return true iff the branch{@link Node} of the given {@link Node} is the {@link Proof}s root{@link Node}. Else false.
    */
   private boolean isBranchNodeRoot(Node node){
      node = getBranchNode(node);
      return node.equals(node.proof().root());
   }
   
}
