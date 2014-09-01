package org.key_project.key4eclipse.resources.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFolder;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

public class IsProofFolderPropertyTester extends PropertyTester {
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if(receiver instanceof IFolder){
         IFolder folder = (IFolder) receiver;
         return (KeYResourcesUtil.isKeYProject(folder.getProject()) && KeYResourcesUtil.isInProofFolder(folder));
      }
      return false;
   }

}
