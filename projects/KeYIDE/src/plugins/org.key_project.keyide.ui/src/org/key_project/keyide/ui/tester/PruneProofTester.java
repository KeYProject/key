package org.key_project.keyide.ui.tester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jface.viewers.TreeSelection;
import org.key_project.keyide.ui.providers.BranchFolder;

import de.uka.ilkd.key.proof.Node;

public class PruneProofTester extends PropertyTester {

   public PruneProofTester() {
      // TODO Auto-generated constructor stub
   }

   @Override
   public boolean test(Object receiver, String property, Object[] args,
         Object expectedValue) {
      if(receiver instanceof TreeSelection){
         TreeSelection selection = (TreeSelection)receiver;
         Object element = selection.getFirstElement();
         if(element instanceof Node){
            return !((Node)element).isClosed();
         }else if(element instanceof BranchFolder){
            return !((BranchFolder)element).isClosed();
         }
         
      }
      return false;
   }

}
