package org.key_project.key4eclipse.resources.ui.propertypages;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;


public class ProofmetaFilter extends ViewerFilter {
   //TODO: Project Explorer filter is not default enabled. The option is activated in the extension, but it doesn't work.
   
   @Override
   public boolean select(Viewer viewer, Object parentElement, Object element) {
      if(element instanceof IFile){
         IFile file = (IFile) element;
         IProject project = file.getProject();
         if(KeYProjectProperties.isHideMetaFiles(project) && KeYResourcesUtil.META_FILE_EXTENSION.equals(file.getFileExtension())){
            return false;
         }
      }
      return true;
   }

}
