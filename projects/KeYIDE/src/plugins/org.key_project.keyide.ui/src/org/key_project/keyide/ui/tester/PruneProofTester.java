package org.key_project.keyide.ui.tester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jface.viewers.TreeSelection;
import org.key_project.keyide.ui.providers.BranchFolder;

import de.uka.ilkd.key.proof.Node;

// TODO: Document class PruneProofTester
public class PruneProofTester extends PropertyTester {
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (receiver instanceof TreeSelection){
         TreeSelection selection = (TreeSelection)receiver;
         Object element = selection.getFirstElement();
         if (element instanceof Node){
            return !((Node)element).isClosed();
         }
         else if (element instanceof BranchFolder){
            return !((BranchFolder)element).isClosed();
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
}
