package org.key_project.keyide.ui.providers;


import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

public class OutlineContentProvider implements ILazyTreeContentProvider{

//   private GUIProofTreeModel model;
   private TreeViewer viewer;

   private ProofTreeListener listener = new ProofTreeListener() {
      
      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofPruned(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofIsBeingPruned(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofExpanded(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
      
      @Override
      public void proofClosed(ProofTreeEvent e) {
         // TODO Auto-generated method stub
         
      }
   };
   
   private boolean autoModeRunning = false;
   
   public  OutlineContentProvider(TreeViewer viewer){
      this.viewer=viewer;
   }
   
   @Override
   public void dispose() {
      // abmelden, sicherstellen das aufgerufen wird
   }

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
//       if(newInput instanceof GUIProofTreeModel){
//         model = (GUIProofTreeModel) newInput;
//         model.register();
//         
//         
//       }
//       if (oldInput != null) {
//          // abmelden
//       }
   }

   @Override
   public Object getParent(Object element) {
      return null;
//      if(element instanceof GUIProofTreeModel){
//         GUIAbstractTreeNode node = (GUIAbstractTreeNode) model.getRoot();
//         System.out.println("getParent Model");
//         return null;
//      }
//      if(element instanceof GUIAbstractTreeNode){
//         GUIAbstractTreeNode node = (GUIAbstractTreeNode) element;
//         System.out.println("getParent Node");
//         return node.getParent();
//      }
//      return null;
   }



   @Override
   public void updateElement(Object parent, int index) {
//      if(parent instanceof GUIProofTreeModel){
//         GUIAbstractTreeNode element = (GUIAbstractTreeNode) ((GUIAbstractTreeNode) ((GUIProofTreeModel) parent).getRoot()).getChildAt(index);
//         viewer.replace(parent, index, element);
//         System.out.println("updateElement Model" + element.toString());
//         updateChildCount(element, -1);
//      }
//      if(parent instanceof GUIAbstractTreeNode){
//         GUIAbstractTreeNode element =  (GUIAbstractTreeNode) ((GUIAbstractTreeNode)parent).getChildAt(index);
//         viewer.replace(parent, index, element);
//         System.out.println("updateElement Node" + element.toString());
//         updateChildCount(element, -1);
//         
//      }
      
   }

   @Override
   public void updateChildCount(Object element, int currentChildCount) {
//      if(element instanceof GUIProofTreeModel){
//         GUIAbstractTreeNode node = (GUIAbstractTreeNode) ((GUIProofTreeModel) element).getRoot();
//         viewer.setChildCount(element, node.getChildCount());
//         System.out.println("updateChild Model " + node.getChildCount() + " " + node.toString());
//      }
//      if(element instanceof GUIAbstractTreeNode){
//         GUIAbstractTreeNode node =  (GUIAbstractTreeNode)element;
//         viewer.setChildCount(element, node.getChildCount());
//         System.out.println("updateChild Node " + node.getChildCount() + " " + node.toString());
//      }
   }
   
   


   
   
}
