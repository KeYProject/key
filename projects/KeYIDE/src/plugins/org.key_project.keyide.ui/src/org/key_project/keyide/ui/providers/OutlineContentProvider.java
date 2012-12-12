package org.key_project.keyide.ui.providers;


import java.util.Vector;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

// TODO: This class is really nice and reusable, rename it into something like ProofTreeLazyTreeContentProvider
// TODO: Refactor source code: first constants (not availbale in this class), than attributes, than constructors, than methods
public class OutlineContentProvider implements ILazyTreeContentProvider{

//   private GUIProofTreeModel model;
   private TreeViewer viewer;
//   private GUIProofTreeModel model;
   private ProofTreeListener listener = new ProofTreeListener() {
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
//         System.out.println("LISTENER -------- SMTDATAUPDATE");
//         updateElement(e.getNode().parent(), e.getNode().parent().getChildNr(e.getNode()));
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFSTRUCTURECHANGED");

         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofPruned(ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFPRUNED");

         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFISBEINGPRUNED");
         
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFGOALSCHANGED");
         // TODO Auto-generated method stub
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalsAdded(final ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFGOALSADDED");
         // TODO Auto-generated method stub
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
//               System.out.println("ADDED----------------------------------------------------------------------------------------------------");
               //System.out.println(e.getGoal());
               
            }
         });
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofGoalRemoved(final ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFGOALREMOVED");
         // TODO Auto-generated method stub
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               //viewer.remove(e.getNode());
//               System.out.println("REMOVED----------------------------------------------------------------------------------------------------");
            }
         });

      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void proofExpanded(final ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFEXPANDED");
         // TODO Auto-generated method stub
         //System.out.println(e.getNode().serialNr());
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               //System.out.println("EXPANDED----------------------------------------------------------------------------------------------------");
               expanded(e.getNode());
            }
            
         });
      }
      
      @Override
      public void proofClosed(final ProofTreeEvent e) {
//         System.out.println("LISTENER -------- PROOFCLOSED");
         // TODO Auto-generated method stub
         Display.getDefault().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               }
         });
      }
   };
   
   
   public  OutlineContentProvider(TreeViewer viewer){
      this.viewer=viewer;
   }
   
   @Override
   public void dispose() {
      // abmelden, sicherstellen das aufgerufen wird
   }

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      if(newInput instanceof Proof){
         Proof proof = (Proof) newInput;
         if(oldInput != null){
            proof.removeProofTreeListener(listener);
         }
          if(newInput != null){
             proof.addProofTreeListener(listener);
          }
          
       }
   }
   
   @Override
   public Object getParent(Object element) {
      return null;

   }


   @Override
   public void updateChildCount(Object element, int currentChildCount) {
      if(element instanceof Proof){
         viewer.setChildCount(element, 1);
         viewer.replace(element, 0, ((Proof)element).root());
      }
   }
   
   @Override
   public void updateElement(Object branch, int index) {
   }
   
   //A vector that saves all branchFolders
   // TODO: Use java naming conventions, rename it into "branchFolders"
   // TODO: If you just needs the BranchFolder for a Node, use a Map: private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();
   private Vector<BranchFolder> BranchFolders = new Vector<BranchFolder>(); // Vector is a bad class because it is based on an array. To store all references of instances a Set is more efficient: private Set<BranchFolder> branchFolders = new HashSet<BranchFolder>();
   
   //manages the whole treeexpandency by calling the specified method for the given node
   private void expanded(Node node){

      if(isBranchNodeRoot(node)){
         expandedRoot(node);
      }
      else expandedFolder(node);
   }
   
 //manages the expandency of the nodes when the branchnode of the given node IS the rootNode 
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
         for(int i = 0; i < node.childrenCount(); i++, size++, index++){
            viewer.replace(node.proof(), size, node.child(i));
         }
      }
   }
   
   //manages the expandency of the nodes when the branchnode of the given node is NOT the rootNode 
   private void expandedFolder(Node node){
      createFolder(node);
      
      BranchFolder branchFolder = getBranchFolder(node);
      int index = getNodeIndexInBranch(node);
      int size = getBranchFolderChildCount(node);
      viewer.setChildCount(branchFolder, size);
      viewer.replace(branchFolder, index, node);
      if(index == size-2 && node.childrenCount() == 1){
         //Updates the "isProved" Status of the Folders to refresh the Images
         updateFolderIsProved(node, branchFolder);
         
         viewer.replace(branchFolder, index+1, node.child(0));
      }
      else if(index == size-1 && node.childrenCount() > 1){
         viewer.setChildCount(branchFolder, size+node.childrenCount());
         for(int i = 0; i < node.childrenCount(); i++, size++, index++){
            viewer.replace(branchFolder, size, node.child(i));
         }
      }
   }
   
   
   //Creates the folder for the branchnode of the given node
   private void createFolder(Node node){
      if(node.parent().childrenCount() > 1){
         Node parentBranchNode = getBranchNode(node.parent());
         BranchFolder parentBranchFolder = getBranchFolder(parentBranchNode);
         int parentIndex = getNodeIndexInBranch(node.parent());
         for(int i = 0; i < node.parent().childrenCount(); i++, parentIndex++){
            if(node.equals(node.parent().child(i))){
               BranchFolder branchFolder = new BranchFolder(parentBranchFolder, node, node.getNodeInfo().getBranchLabel());
               BranchFolders.add(branchFolder);
               if(parentBranchFolder == null)
                  viewer.replace(node.proof(), parentIndex+1, branchFolder);
               else viewer.replace(parentBranchFolder, parentIndex+1, branchFolder);
            }
         }   
      }
   }
   
   //Updates the first Folder above a "closed goal" term and calls the setUpperFoldersProved(Node node) method to check the upper folders for provedheit
   private void updateFolderIsProved(Node node, BranchFolder branchFolder){
      if(node.child(0).name().equals("Closed goal")){
         branchFolder.setProved(true);
         if(branchFolder.getParent() == null)
            viewer.replace(node.proof(), getBranchFolderIndex(branchFolder), branchFolder);
         else
            viewer.replace(branchFolder.getParent(), getBranchFolderIndex(branchFolder), branchFolder);
         setUpperFoldersProved(node.child(0));
      }
   }

   
   //checks if the upper folders are proved and sets their status
   //TODO call with parent of checked folders
   private void setUpperFoldersProved(Node node){
      
      if(!getBranchNode(node).equals(node.proof().root())){
         boolean setProved = false;
         Node branchNode = getBranchNode(node);
         Node parentNode = branchNode.parent();
         for(int i = 0; i < parentNode.childrenCount(); i++){
            if(getBranchFolder(parentNode.child(i)) != null){
               if(getBranchFolder(parentNode.child(i)).isProved())
                  setProved = true;
               else setProved = false;
            }
         }
         if(setProved){
            Node parentBranchNode = getBranchNode(parentNode);
            
            for(int i = 0; i < BranchFolders.size(); i++){ // Never iterate over a Collection like this, because not every implementation has a direct access to children via an index. Use always the iterator concept: for (BranchFolders folder : BranchFolders) {...} 
               if(BranchFolders.get(i).getChild().equals(parentBranchNode)){
                  BranchFolders.get(i).setProved(true);
                  if(BranchFolders.get(i).getParent() == null)
                     viewer.replace(node.proof(), getBranchFolderIndex(BranchFolders.get(i)), BranchFolders.get(i));
                  else
                     viewer.replace(BranchFolders.get(i).getParent(), getBranchFolderIndex(BranchFolders.get(i)), BranchFolders.get(i));
               }
            }
            setUpperFoldersProved(parentNode);
         }
      } 
   }
   
   //returns the index of a given branchfolder in its branchfolder parent
   private int getBranchFolderIndex(BranchFolder branchFolder){
      Node parentNode = branchFolder.getChild().parent();
      for(int i = 0; i < parentNode.childrenCount(); i++){
         if(branchFolder.getLabel().equals(parentNode.child(i).getNodeInfo().getBranchLabel()))
            return getNodeIndexInBranch(parentNode)+i+1;
      }
      return -1;
   }
   
   //Returns the BranchNode of the given node
   private Node getBranchNode(Node node){
      if(node.equals(node.proof().root()))
         return node.proof().root();
      else if(node.parent().childrenCount() > 1)
         return node;
      else return getBranchNode(node.parent());
   }
   
   //returns the childcount of the folder of a given note. the count does NOT includes subFolders!
   private int getBranchFolderChildCount(Node node){
      Node branchNode = getBranchNode(node);
      int count = 1;
      while(branchNode.childrenCount() == 1){
         branchNode = branchNode.child(0);
         count += 1;
      }
      return count;
   }
   
   //returns the branchfolder of a given node
   private BranchFolder getBranchFolder(Node node){
      Node branchNode = getBranchNode(node);
      for(int i = 0; i < BranchFolders.size(); i++){
         if(BranchFolders.get(i).getChild().equals(branchNode)){
            return BranchFolders.get(i);
         }
      }
      return null;
   }
   
   //returns the index in the given node in its branch
   private int getNodeIndexInBranch(Node node){
      Node branchNode = getBranchNode(node);
      int count = 0;
      while(!node.equals(branchNode) && branchNode.childrenCount() == 1){
         branchNode = branchNode.child(0);
         count += 1;
      }
      return count;
   }
   
   //returns iff the branchnode of the given node is the rootNode
   private boolean isBranchNodeRoot(Node node){
      node = getBranchNode(node);
      return node.equals(node.proof().root());
   }
   
   //returns if the folder for the given branchnode already exists
   //not needed atm. can be deleted
   private boolean hasFolder(Node branchNode){
      for(int i = 0; i < BranchFolders.size(); i++){
         if(BranchFolders.get(i).getChild().equals(branchNode)){
            return true;
         }
      }
      return false;
   }
   
   
   
}
