package org.key_project.key4eclipse.resources.ui.propertypages;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;


public class ProofmetaFilter extends ViewerFilter {
   
   @Override
   public boolean select(Viewer viewer, Object parentElement, Object element) {
      if(element instanceof IFile){
         IFile file = (IFile) element;
         if(KeYResourcesUtil.META_FILE_EXTENSION.equals(file.getFileExtension())){
            return false;
         }
      }
      return true;
   }

}
