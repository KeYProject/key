package org.key_project.key4eclipse.resources.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

public class IsProofFilePropertyTester extends PropertyTester {
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if(receiver instanceof IFile){
         IFile file = (IFile) receiver;
         if (KeYResourcesUtil.isInProofFolder(file) && 
             KeYResourcesUtil.PROOF_FILE_EXTENSION.equals(file.getFileExtension())){
            try {
               return KeYResourcesUtil.isKeYProject(file.getProject());
            }
            catch (CoreException e){
               LogUtil.getLogger().logError(e);
            }
         }
      }
      return false;
   }

}
