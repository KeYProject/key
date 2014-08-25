package org.key_project.key4eclipse.resources.ui.expression;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

public class IsProofFilePropertyTester extends PropertyTester {

   @Override
   public boolean test(Object receiver, String property, Object[] args,
         Object expectedValue) {
      if(receiver instanceof IFile){
         IFile file = (IFile) receiver;
         if(KeYResourcesUtil.isInProofFolder(file) && "proof".equals(file.getFileExtension())){
            try{
               IProjectDescription desc = file.getProject().getDescription();
               if(desc.hasNature("org.key_project.key4eclipse.resources.KeYProjectNature")){
                  return true;
               }
            } catch (CoreException e){
               return false;
            }
         }
      }
      return false;
   }

}
