package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.internal.resources.Folder;
import org.eclipse.core.internal.resources.Project;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.jobs.ISchedulingRule;

public class MutexRule implements ISchedulingRule{
      
   @Override
   public boolean contains(ISchedulingRule rule) {
      if(rule != null){
         if(rule instanceof Folder){
            IFolder ruleFolder = (IFolder) rule;
            IFolder proofFolder = ruleFolder.getProject().getFolder("proofs");
            if(proofFolder.exists()){
               return proofFolder.getFullPath().isPrefixOf(ruleFolder.getFullPath());
            }
            else{
               return false;
            }
         }
         else if(rule instanceof Project){
            return true;
         }
      }
      return (rule == this);
   }

   @Override
   public boolean isConflicting(ISchedulingRule rule) {
      return (rule == this);
   }

}
