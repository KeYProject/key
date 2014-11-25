package org.key_project.util.jmlediting;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

/**
 * UtilClass to provide general utility-Methods in the jmlEditing-Project
 * 
 * @author Thomas Glaser
 *
 */
public class JMLUtil {
   
   /**
    * prevent Instantiations
    */
   private JMLUtil() {}
   
   /**
    * Get the current active IProject 
    * 
    * @return IProject
    *             the current active IProject
    */
   public static IProject getCurrentProject() {
      IProject project = null;
      
      IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
      IWorkbenchPage activePage = window.getActivePage();
      IEditorPart editorPart = activePage.getActiveEditor();
      IResource resource = (IResource) editorPart.getEditorInput().getAdapter(IResource.class);
      if (resource != null) {
         project = resource.getProject();
      }
      return project;
   }
}
