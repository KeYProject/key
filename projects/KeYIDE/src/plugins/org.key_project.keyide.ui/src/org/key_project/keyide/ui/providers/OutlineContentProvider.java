package org.key_project.keyide.ui.providers;


import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.internal.ole.win32.COSERVERINFO;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.TreeItem;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

// TODO: This class is really nice and reusable, rename it into something like ProofTreeLazyTreeContentProvider
// TODO: Refactor source code: first constants (not availbale in this class), than attributes, than constructors, than methods
public class OutlineContentProvider implements ILazyTreeContentProvider{

   private KeYEnvironment<CustomConsoleUserInterface> environment;
   private Proof proof;
   private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();
   private boolean isAutoModeRunning = false;
//   private GUIProofTreeModel model;
   private TreeViewer viewer;
//   private GUIProofTreeModel model;
   
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         isAutoModeRunning = false;
         // TODO Refresh the tree
         viewer.getControl().getDisplay().asyncExec(new Runnable() {
            
            @Override
            public void run() {
               // TODO Auto-generated method stub
               viewer.refresh();
            }
         });
         
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
         isAutoModeRunning = true;
      }
   };
   
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
//               System.out.println("Added: " + e.getNode());
               
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
//               System.out.println("Removed: " + e.getGoal().node().serialNr() + ":" + e.getGoal().node().name());
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
//               System.out.println("Expanded: " + e.getNode().serialNr() + ":" + e.getNode().name());
               if(!isAutoModeRunning){
                  expanded(e.getNode());
               }
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
   
   
   public  OutlineContentProvider(TreeViewer viewer, KeYEnvironment<CustomConsoleUserInterface> environment, Proof proof){
      this.viewer=viewer;
      this.proof = proof;
      this.environment = environment;
   }
   
   
   
   @Override
   public void dispose() {
      // TODO abmelden, sicherstellen das aufgerufen wird
//      proof.removeProofTreeListener(listener);
//      if (environment != null){
//      environment.getMediator().removeAutoModeListener(autoModeListener);
//      }
   }
      

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      if(newInput instanceof Proof){
         this.proof = (Proof) newInput;
         if(oldInput != null){
            proof.removeProofTreeListener(listener);
            if (environment != null) {
               environment.getMediator().removeAutoModeListener(autoModeListener);
            }
         }
          if(newInput != null){
             proof.addProofTreeListener(listener);
             if (environment != null) {
                environment.getMediator().addAutoModeListener(autoModeListener);
             }
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
         System.out.println("UpdateChildCount: Proof");
         Node node = ((Proof)element).root();
         System.out.println(getBranchFolderChildCount(node));
         viewer.setChildCount(element, getBranchFolderChildCount(node));
         
      }
      else if(element instanceof Node){
         Node node = (Node) element;
         System.out.println("UpdateChildCount: " + node.serialNr() + ":" + node.name());
         
         
      }
   }
   
   @Override
   public void updateElement(Object parent, int index) {
      if(parent instanceof Proof){
         System.out.println("UpdateElement: Proof");
      }
      else if(parent instanceof Node){
         Node node = (Node) parent;
         System.out.println("UpdateElement: " + node.serialNr() + ":" + node.name());
      }
   }
   
   // TODO: If you just needs the BranchFolder for a Node, use a Map: private Map<Node, BranchFolder> branchFolders = new HashMap<Node, BranchFolder>();
   //private Vector<BranchFolder> branchFolders = new Vector<BranchFolder>(); // Vector is a bad class because it is based on an array. To store all references of instances a Set is more efficient: private Set<BranchFolder> branchFolders = new HashSet<BranchFolder>();
   
   //manages the whole treeexpandency by calling the specified method for the given node
   private void expanded(Node node){

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
//         for(int i = 0; i < node.childrenCount(); i++, size++, index++){
//            viewer.replace(node.proof(), size, node.child(i));
//         }
         createFolder(node);
      }
   }
   
   //manages the expandency of the nodes when the branchnode of the given node is NOT the rootNode 
   private void expandedFolder(Node node){
      //createFolder(node);
      
      BranchFolder branchFolder = getBranchFolder(node);
      int index = getNodeIndexInBranch(node);
      int size = getBranchFolderChildCount(node);
      viewer.setChildCount(branchFolder, size);
      viewer.replace(branchFolder, index, node);
      if(index == size-2 && node.childrenCount() == 1){
         //Updates the "isProved" Status of the Folders to refresh the Images         
         viewer.replace(branchFolder, index+1, node.child(0));
      }
      else if(index == size-1 && node.childrenCount() > 1){
         viewer.setChildCount(branchFolder, size+node.childrenCount());
//         for(int i = 0; i < node.childrenCount(); i++, size++, index++){
//            viewer.replace(branchFolder, size, node.child(i));
//         }
         createFolder(node);
      }
   }
   
   
   //Creates the folder for the branchnode of the given node
   private void createFolder(Node node){
      for(int i = 0; i < node.childrenCount(); i++){
         BranchFolder parentBranchFolder = getBranchFolder(node);
         BranchFolder branchFolder = new BranchFolder(parentBranchFolder, node.child(i));
         branchFolders.put(node.child(i), branchFolder);
//         System.out.println(node.child(i).serialNr() + ":" + node.child(i).name() + " | " + node.child(i).getNodeInfo().getBranchLabel());
         int nodeIndex = getNodeIndexInBranch(node);
         if(parentBranchFolder == null)
            viewer.replace(node.proof(), nodeIndex+i+1, branchFolder);
         else
            viewer.replace(parentBranchFolder, nodeIndex+i+1, branchFolder);
         viewer.setChildCount(branchFolder, 1);
         viewer.replace(branchFolder,0 , node.child(i));
      }
//      if(node.parent().childrenCount() > 1){
//         Node parentBranchNode = getBranchNode(node.parent());
//         BranchFolder parentBranchFolder = getBranchFolder(parentBranchNode);
//         int parentIndex = getNodeIndexInBranch(node.parent());
//         for(int i = 0; i < node.parent().childrenCount(); i++, parentIndex++){
//            if(node.equals(node.parent().child(i))){
//               BranchFolder branchFolder = new BranchFolder(parentBranchFolder, node, node.getNodeInfo().getBranchLabel());
//               branchFolders.put(node, branchFolder);
//               if(parentBranchFolder == null)
//                  viewer.replace(node.proof(), parentIndex+1, branchFolder);
//               else viewer.replace(parentBranchFolder, parentIndex+1, branchFolder);
//            }
//         }   
//      }
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
      if(branchNode.equals(node.proof().root()))
         return null;
      else
         return branchFolders.get(branchNode);
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
   
}
