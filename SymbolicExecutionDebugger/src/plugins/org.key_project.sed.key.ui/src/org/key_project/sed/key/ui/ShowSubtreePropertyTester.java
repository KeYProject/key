package org.key_project.sed.key.ui;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Node;

public class ShowSubtreePropertyTester extends PropertyTester {

   public static final String IS_SUBTREE_SUPPORTED = "isShowSubtreeSupported";

   @Override
   public boolean test(Object receiver, String property, Object[] args,
         Object expectedValue) {
      if (receiver instanceof IStructuredSelection) {
         if (property.equals(IS_SUBTREE_SUPPORTED)) {
            IStructuredSelection selection = (IStructuredSelection) receiver;
            Object element = SWTUtil.getFirstElement(selection);
            if (element instanceof Node) {
               return true;
            } 
         }
      }
      return false;
   }

}
