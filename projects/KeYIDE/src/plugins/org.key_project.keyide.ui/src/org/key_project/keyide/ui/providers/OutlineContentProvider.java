package org.key_project.keyide.ui.providers;


import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;

import de.uka.ilkd.key.gui.prooftree.GUIAbstractTreeNode;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;

public class OutlineContentProvider implements ILazyTreeContentProvider{

   
   TreeViewer viewer;
   int i = 0;
   public  OutlineContentProvider(TreeViewer viewer){
      this.viewer=viewer;
   }
   
   @Override
   public void dispose() {
   }

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
   }

   @Override
   public Object getParent(Object element) {
      if(element instanceof GUIAbstractTreeNode){
         GUIAbstractTreeNode node = (GUIAbstractTreeNode) element;
         System.out.println("getParent" + i);
         i++;
         return node.getParent();
      }
      return null;
   }



   @Override
   public void updateElement(Object parent, int index) {
      if(parent instanceof GUIAbstractTreeNode){
         GUIAbstractTreeNode element =  (GUIAbstractTreeNode) ((GUIAbstractTreeNode)parent).getChildAt(index);
         viewer.replace(parent, index, element);
         System.out.println("updateElement Node" + element.toString());
         i++;
         updateChildCount(element, -1);
         
      }
      
   }

   @Override
   public void updateChildCount(Object element, int currentChildCount) {
      if(element instanceof GUIAbstractTreeNode){
         GUIAbstractTreeNode node =  (GUIAbstractTreeNode)element;
         viewer.setChildCount(element, node.getChildCount());
         System.out.println("updateChild Node " + node.getChildCount() + " " + node.toString());
         i++;
      }
   }
   
   


   
   
}
