package org.key_project.keyide.ui.providers;

import org.eclipse.jface.viewers.LabelProvider;

import de.uka.ilkd.key.gui.prooftree.*;

public class OutlineLabelProvider extends LabelProvider {

   
   public String getText(Object element){
      if(element instanceof GUIProofTreeModel){
         System.out.println("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
      }
      if(element instanceof GUIAbstractTreeNode){
         return ((GUIAbstractTreeNode)element).toString();
      }
      return null;
   }
}
