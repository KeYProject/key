package org.key_project.key4eclipse.resources.property;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

public final class KeYProjectProperties {

   public static final QualifiedName PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT = new QualifiedName("org.key_project.key4eclipse.resources", "enableEfficientProofManagement");

   public static enum EnableEfficientProofManagement{
      ENALBLE_EFFICIENT_PROOFMANAGEMENT,
      DISALBLE_EFFICIENT_PROOFMANAGEMENT
   }
   
   public static void setEnableEfficientProofManagement(IProject project,  String enabled) throws CoreException{
      if(project != null){
         project.setPersistentProperty(PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT, enabled);
      }
   }
}
