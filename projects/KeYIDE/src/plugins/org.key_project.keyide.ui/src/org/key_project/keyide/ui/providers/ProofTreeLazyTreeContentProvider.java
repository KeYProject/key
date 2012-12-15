package org.key_project.keyide.ui.providers;


import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
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
public class ProofTreeLazyTreeContentProvider implements ILazyTreeContentProvider{

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private Proof proof;
   private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();
   @SuppressWarnings("unused")
   private boolean isAutoModeRunning = false;
   private TreeViewer viewer;
   
   
   /**
    * The Constructor
    * @param viewer
    * @param environment
    * @param proof
    */
   // TODO Comment
   public  ProofTreeLazyTreeContentProvider(TreeViewer viewer, KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof){
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
         isAutoModeRunning = false;
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
         isAutoModeRunning = true;
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
      public void proofPruned(ProofTreeEvent e) {
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
         System.out.println("ChildCount Node");
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
      updateChildCount(element, -1);
   }
   
   
   /**
    * Removes the added listeners.
    */
   @Override
   public void dispose() {
      // TODO abmelden, sicherstellen das aufgerufen wird
   }
   
   
// Shell muss sichtbar sein
//TreeViewer x = new TreeViewer();
//x.setUseHashlookup(true);
//x.setInput(input); //;
//x.expandAll();
//TreeItem[] items = x.getTree().getItems()
//for (TreeItem item : items) {
// x.getTree().showItem(item);
// x.expandAll();
//   item.getItems()
//   item.getData() == node, or folder
//}


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
