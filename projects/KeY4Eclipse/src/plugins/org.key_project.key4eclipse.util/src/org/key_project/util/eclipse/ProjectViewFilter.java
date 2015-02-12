package org.key_project.util.eclipse;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.key_project.util.java.ArrayUtil;

/**
 * A {@link ViewerFilter} which accepts only specified {@link IProject}s 
 * and their child {@link IResource}s.
 * @author Martin Hentschel
 */
public class ProjectViewFilter extends ViewerFilter {
   /**
    * The {@link IProject}s to accept.
    */
   private final IProject[] acceptedProject;
   
   /**
    * Constructor.
    * @param acceptedProject The {@link IProject}s to accept.
    */
   public ProjectViewFilter(IProject... acceptedProject) {
      this.acceptedProject = acceptedProject;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean select(Viewer viewer, Object parentElement, Object element) {
      if (element instanceof IResource) {
         IProject currentProject = ((IResource) element).getProject();
         return ArrayUtil.contains(acceptedProject, currentProject);
      }
      else {
         return false;
      }
   }
}
